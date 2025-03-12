#include "llvm/ADT/StringRef.h"
#include "llvm/CodeGen/Passes.h"
#include "llvm/ExecutionEngine/ExecutionEngine.h"
#include "llvm/ExecutionEngine/Orc/LLJIT.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Value.h"
#include "llvm/IR/Verifier.h"
#include "llvm/MC/TargetRegistry.h"
#include "llvm/Support/CodeGen.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Target/TargetMachine.h"
#include "llvm/Target/TargetOptions.h"
#include "llvm/TargetParser/Host.h"
#include <cctype>
#include <iostream>
#include <llvm-c/TargetMachine.h>
#include <map>
#include <memory>
#include <string>
#include <vector>

using namespace llvm;
using namespace std;

// Global LLVM Variables
unique_ptr<LLVMContext> TheContext;
unique_ptr<IRBuilder<>> Builder;
unique_ptr<Module> TheModule;
map<string, AllocaInst *> NamedValues;
map<string, Function *> FunctionRegistry;

// Token Types
enum class TokenType {
  Identifier,
  Number,
  Operator,
  EndOfFile,
  Unknown,
  // Adding keywords and symbols for function definitions
  Def,
  OpenParen,
  CloseParen,
  Comma,
  Semicolon,
  OpenBrace,
  CloseBrace
};

struct Token {
  TokenType type;
  string value;
  Token(TokenType t, string v) : type(t), value(std::move(v)) {}
};

// Lexer
class Lexer {
private:
  StringRef Source;
  size_t Index = 0;

public:
  explicit Lexer(StringRef Src) : Source(Src) {}

  vector<Token> tokenize() {
    vector<Token> tokens;
    while (Index < Source.size()) {
      char c = Source[Index];
      if (isspace(c)) {
        Index++;
      } else if (isalpha(c)) {
        tokens.push_back(lexIdentifierOrKeyword());
      } else if (isdigit(c)) {
        tokens.push_back(lexNumber());
      } else if (c == '(') {
        tokens.push_back(Token(TokenType::OpenParen, "("));
        Index++;
      } else if (c == ')') {
        tokens.push_back(Token(TokenType::CloseParen, ")"));
        Index++;
      } else if (c == '{') {
        tokens.push_back(Token(TokenType::OpenBrace, "{"));
        Index++;
      } else if (c == '}') {
        tokens.push_back(Token(TokenType::CloseBrace, "}"));
        Index++;
      } else if (c == ',') {
        tokens.push_back(Token(TokenType::Comma, ","));
        Index++;
      } else if (c == ';') {
        tokens.push_back(Token(TokenType::Semicolon, ";"));
        Index++;
      } else if (ispunct(c)) {
        tokens.push_back(Token(TokenType::Operator, string(1, c)));
        Index++;
      } else {
        tokens.emplace_back(TokenType::Unknown, string(1, c));
        Index++;
      }
    }
    tokens.emplace_back(TokenType::EndOfFile, "EOF");
    return tokens;
  }

private:
Token lexIdentifierOrKeyword() {
    size_t start = Index;
    while (Index < Source.size() && isalnum(Source[Index]))
      Index++;
    string identifier = Source.slice(start, Index).str();
  
    // Check for keywords
    if (identifier == "def") {
      return Token(TokenType::Def, identifier);
    }
  
    return Token(TokenType::Identifier, identifier);
  }

  Token lexNumber() {
    size_t start = Index;
    while (Index < Source.size() && isdigit(Source[Index]))
      Index++;
    return Token(TokenType::Number, Source.slice(start, Index).str());
  }
};

// AST Nodes
class ExprAST {
public:
  virtual ~ExprAST() = default;
  virtual Value *codegen() = 0;
};

class NumberExprAST : public ExprAST {
  double Val;

public:
  explicit NumberExprAST(double Val) : Val(Val) {}

  Value *codegen() override {
    return ConstantFP::get(*TheContext, APFloat(Val));
  }
};

class VariableExprAST : public ExprAST {
  string Name;

public:
  explicit VariableExprAST(const string &Name) : Name(Name) {}

  const string &getName() const { return Name; } // Getter function

  Value *codegen() override {
    // Look this variable up in the function
    AllocaInst *A = NamedValues[Name];
    if (!A) {
      // Auto-create variables that are referenced but not declared
      Function *TheFunction = Builder->GetInsertBlock()->getParent();
      AllocaInst *Alloca = Builder->CreateAlloca(Type::getDoubleTy(*TheContext),
                                                 nullptr, Name.c_str());
      Builder->CreateStore(ConstantFP::get(*TheContext, APFloat(0.0)), Alloca);
      NamedValues[Name] = Alloca;
      errs() << "Note: Auto-initializing undefined variable " << Name
             << " to 0.0\n";
      A = Alloca;
    }

    return Builder->CreateLoad(Type::getDoubleTy(*TheContext), A, Name.c_str());
  }
};

class BinaryExprAST : public ExprAST {
  char Op;
  unique_ptr<ExprAST> LHS, RHS;

public:
  BinaryExprAST(char Op, unique_ptr<ExprAST> LHS, unique_ptr<ExprAST> RHS)
      : Op(Op), LHS(std::move(LHS)), RHS(std::move(RHS)) {}

  Value *codegen() override {
    // Special case for assignment
    if (Op == '=') {
      auto *VarExpr = dynamic_cast<VariableExprAST *>(LHS.get());
      if (!VarExpr) {
        errs() << "Error: Left-hand side of assignment must be a variable.\n";
        return nullptr;
      }

      Value *R = RHS->codegen();
      if (!R)
        return nullptr;

      const string &VarName = VarExpr->getName();

      if (NamedValues.find(VarName) == NamedValues.end()) {
        Function *TheFunction = Builder->GetInsertBlock()->getParent();
        AllocaInst *Alloca = Builder->CreateAlloca(
            Type::getDoubleTy(*TheContext), nullptr, VarName.c_str());
        NamedValues[VarName] = Alloca;
      }

      Builder->CreateStore(R, NamedValues[VarName]);
      return R;
    }

    Value *L = LHS->codegen();
    Value *R = RHS->codegen();
    if (!L || !R)
      return nullptr;

    switch (Op) {
    case '+':
      return Builder->CreateFAdd(L, R, "addtmp");
    case '-':
      return Builder->CreateFSub(L, R, "subtmp");
    case '*':
      return Builder->CreateFMul(L, R, "multmp");
    case '/':
      return Builder->CreateFDiv(L, R, "divtmp");
    default:
      errs() << "Error: Invalid binary operator '" << Op << "'\n";
      return nullptr;
    }
  }
};

// Function Call Expression
class CallExprAST : public ExprAST {
  string Callee;
  vector<unique_ptr<ExprAST>> Args;

public:
  CallExprAST(const string &Callee, vector<unique_ptr<ExprAST>> Args)
      : Callee(Callee), Args(std::move(Args)) {}

  Value *codegen() override {
    // Look up the function name in the global module table
    Function *CalleeF = TheModule->getFunction(Callee);
    if (!CalleeF) {
      errs() << "Error: Unknown function referenced: " << Callee << "\n";
      return nullptr;
    }

    // Check argument count
    if (CalleeF->arg_size() != Args.size()) {
      errs() << "Error: Incorrect number of arguments passed. Expected "
             << CalleeF->arg_size() << ", got " << Args.size() << "\n";
      return nullptr;
    }

    vector<Value *> ArgsV;
    for (unsigned i = 0, e = Args.size(); i != e; ++i) {
      ArgsV.push_back(Args[i]->codegen());
      if (!ArgsV.back())
        return nullptr;
    }

    return Builder->CreateCall(CalleeF, ArgsV, "calltmp");
  }
};

// Function Prototype
class PrototypeAST {
    string Name;
    vector<string> Args;
    vector<unique_ptr<ExprAST>> DefaultValues; // Store default values
  
  public:
    PrototypeAST(const string &Name, vector<string> Args, 
                 vector<unique_ptr<ExprAST>> Defaults)
        : Name(Name), Args(std::move(Args)), DefaultValues(std::move(Defaults)) {}
  
    const string &getName() const { return Name; }
    const vector<string> &getArgs() const { return Args; }
    const vector<unique_ptr<ExprAST>> &getDefaults() const { return DefaultValues; }
  
    Function *codegen() {
      // Create a function type: double(double, double, ...) etc.
      vector<Type *> Doubles(Args.size(), Type::getDoubleTy(*TheContext));
      FunctionType *FT =
          FunctionType::get(Type::getDoubleTy(*TheContext), Doubles, false);
  
      Function *F =
          Function::Create(FT, Function::ExternalLinkage, Name, TheModule.get());
  
      // Set names for all arguments
      unsigned Idx = 0;
      for (auto &Arg : F->args())
        Arg.setName(Args[Idx++]);
  
      return F;
    }
  };

// Function Definition
class FunctionAST {
  unique_ptr<PrototypeAST> Proto;
  unique_ptr<ExprAST> Body;

public:
  FunctionAST(unique_ptr<PrototypeAST> Proto, unique_ptr<ExprAST> Body)
      : Proto(std::move(Proto)), Body(std::move(Body)) {}

  Function *codegen() {
    // Check for an existing function from a previous 'extern' declaration
    Function *TheFunction = TheModule->getFunction(Proto->getName());
    
    if (!TheFunction)
      TheFunction = Proto->codegen();
    
    if (!TheFunction)
      return nullptr;
    
    // Create a new basic block to start insertion into
    BasicBlock *BB = BasicBlock::Create(*TheContext, "entry", TheFunction);
    Builder->SetInsertPoint(BB);
    
    // Record the function arguments in the NamedValues map
    NamedValues.clear();
    
    // Get argument names and default values
    const auto &ArgNames = Proto->getArgs();
    const auto &DefaultValues = Proto->getDefaults();
    
    unsigned Idx = 0;
    for (auto &Arg : TheFunction->args()) {
      // Create an alloca for this variable
      AllocaInst *Alloca = Builder->CreateAlloca(Type::getDoubleTy(*TheContext),
                                                 nullptr, Arg.getName());
  
      // Store the initial value into the alloca
      Builder->CreateStore(&Arg, Alloca);
  
      // Add arguments to variable symbol table
      NamedValues[std::string(Arg.getName())] = Alloca;
      Idx++;
    }
    
    if (Value *RetVal = Body->codegen()) {
      // Finish off the function
      Builder->CreateRet(RetVal);
  
      // Validate the generated code, checking for consistency
      verifyFunction(*TheFunction);
  
      // Add to function registry
      FunctionRegistry[Proto->getName()] = TheFunction;
  
      return TheFunction;
    }
    
    // Error reading body, remove function
    TheFunction->eraseFromParent();
    return nullptr;
  }
};

// Parser
class Parser {
private:
  vector<Token> Tokens;
  size_t CurrentIndex = 0;

  Token getCurrentToken() {
    if (CurrentIndex >= Tokens.size())
      return Token(TokenType::EndOfFile, "EOF");
    return Tokens[CurrentIndex];
  }

  void consumeToken() {
    if (CurrentIndex < Tokens.size())
      CurrentIndex++;
  }

  // Get operator precedence
  int getOpPrecedence(char op) {
    switch (op) {
    case '=':
      return 10; // Lowest precedence
    case '+':
    case '-':
      return 20;
    case '*':
    case '/':
      return 40; // Highest precedence
    default:
      return -1; // Not an operator
    }
  }

public:
  explicit Parser(vector<Token> tokens) : Tokens(std::move(tokens)) {}

  unique_ptr<ExprAST> parseExpression() {
    auto LHS = parsePrimary();
    if (!LHS)
      return nullptr;
    return parseBinaryOpRHS(0, std::move(LHS));
  }

  // Parse a function definition
  unique_ptr<FunctionAST> parseDefinition() {
    consumeToken(); // consume 'def'

    auto Proto = parsePrototype();
    if (!Proto)
      return nullptr;

    // Expect and consume opening brace
    if (getCurrentToken().type != TokenType::OpenBrace) {
      errs() << "Expected '{' in function definition\n";
      return nullptr;
    }
    consumeToken();

    // Parse the function body
    auto Body = parseExpression();
    if (!Body)
      return nullptr;

    // Expect and consume closing brace
    if (getCurrentToken().type != TokenType::CloseBrace) {
      errs() << "Expected '}' in function definition\n";
      return nullptr;
    }
    consumeToken();

    return make_unique<FunctionAST>(std::move(Proto), std::move(Body));
  }

  // Parse the top level of our program
  void parseTopLevel() {
    while (getCurrentToken().type != TokenType::EndOfFile) {
      switch (getCurrentToken().type) {
      case TokenType::Def:
        if (auto FnAST = parseDefinition()) {
          if (auto *FnIR = FnAST->codegen()) {
            outs() << "Parsed a function definition.\n";
          }
        } else {
          // Skip token for error recovery
          consumeToken();
        }
        break;
      default:
        // Parse top-level expressions
        if (auto E = parseExpression()) {
          if (auto *V = E->codegen()) {
            outs() << "Parsed a top-level expression.\n";
          }
        } else {
          // Skip token for error recovery
          consumeToken();
        }

        // Consume any trailing semicolon
        if (getCurrentToken().type == TokenType::Semicolon) {
          consumeToken();
        }
        break;
      }
    }
  }

private:
  // Parse a function prototype
  unique_ptr<PrototypeAST> parsePrototype() {
    if (getCurrentToken().type != TokenType::Identifier) {
      errs() << "Expected function name in prototype\n";
      return nullptr;
    }
  
    string FnName = getCurrentToken().value;
    consumeToken();
  
    if (getCurrentToken().type != TokenType::OpenParen) {
      errs() << "Expected '(' in prototype\n";
      return nullptr;
    }
    consumeToken();
  
    // Read the arguments
    vector<string> ArgNames;
    vector<unique_ptr<ExprAST>> DefaultValues;
    
    while (getCurrentToken().type == TokenType::Identifier) {
      string ArgName = getCurrentToken().value;
      ArgNames.push_back(ArgName);
      consumeToken();
  
      // Check for default value assignment
      if (getCurrentToken().type == TokenType::Operator && 
          getCurrentToken().value == "=") {
        consumeToken(); // consume '='
        
        // Parse the default value expression
        auto DefaultExpr = parsePrimary();
        if (!DefaultExpr) {
          errs() << "Invalid default value for parameter '" << ArgName << "'\n";
          return nullptr;
        }
        // Store the default value for this parameter
      DefaultValues.push_back(std::move(DefaultExpr));
    } else {
      // No default value specified, use nullptr as placeholder
      DefaultValues.push_back(nullptr);
    }

    if (getCurrentToken().type == TokenType::Comma) {
        consumeToken();
      } else if (getCurrentToken().type == TokenType::CloseParen) {
        break;
      } else {
        errs() << "Expected ',' or ')' in argument list\n";
        return nullptr;
      }
    }
  
    // Consume the closing parenthesis
    if (getCurrentToken().type != TokenType::CloseParen) {
      errs() << "Expected ')' in prototype\n";
      return nullptr;
    }
    consumeToken();
  
    return make_unique<PrototypeAST>(FnName, std::move(ArgNames), std::move(DefaultValues));
  }

  unique_ptr<ExprAST> parsePrimary() {
    Token tok = getCurrentToken();

    switch (tok.type) {
    case TokenType::Identifier: {
      string IdName = tok.value;
      consumeToken();

      // Simple variable reference
      if (getCurrentToken().type != TokenType::OpenParen)
        return make_unique<VariableExprAST>(IdName);

      // Function call
      consumeToken(); // eat '('
      vector<unique_ptr<ExprAST>> Args;

      if (getCurrentToken().type != TokenType::CloseParen) {
        while (true) {
          if (auto Arg = parseExpression())
            Args.push_back(std::move(Arg));
          else
            return nullptr;

          if (getCurrentToken().type == TokenType::CloseParen)
            break;

          if (getCurrentToken().type != TokenType::Comma) {
            errs() << "Expected ')' or ',' in argument list\n";
            return nullptr;
          }
          consumeToken();
        }
      }

      // Eat the ')'
      consumeToken();

      return make_unique<CallExprAST>(IdName, std::move(Args));
    }
    case TokenType::Number: {
      consumeToken();
      return make_unique<NumberExprAST>(stod(tok.value));
    }
    case TokenType::OpenParen: {
      consumeToken(); // eat '('
      auto V = parseExpression();
      if (!V)
        return nullptr;

      if (getCurrentToken().type != TokenType::CloseParen) {
        errs() << "Expected ')'\n";
        return nullptr;
      }

      consumeToken(); // eat ')'
      return V;
    }
    default:
      errs() << "Unknown token when expecting an expression: " << tok.value
             << "\n";
      return nullptr;
    }
  }

  unique_ptr<ExprAST> parseBinaryOpRHS(int ExprPrec, unique_ptr<ExprAST> LHS) {
    // Keep looking for operators as long as we have tokens
    while (true) {
      Token tok = getCurrentToken();

      // If end of input or not an operator, we're done
      if (tok.type != TokenType::Operator)
        return LHS;

      char Op = tok.value[0];
      int TokPrec = getOpPrecedence(Op);

      // If this operator binds at least as tightly as the current one,
      // consume it, otherwise we're done
      if (TokPrec < ExprPrec)
        return LHS;

      // Consume the operator
      consumeToken();

      // Parse the primary expression after the operator
      auto RHS = parsePrimary();
      if (!RHS)
        return nullptr;

      // If BinOp binds less tightly with RHS than the operator after RHS,
      // let the pending operator take RHS as its LHS
      Token NextTok = getCurrentToken();
      if (NextTok.type == TokenType::Operator) {
        int NextPrec = getOpPrecedence(NextTok.value[0]);
        if (TokPrec < NextPrec) {
          RHS = parseBinaryOpRHS(TokPrec + 1, std::move(RHS));
          if (!RHS)
            return nullptr;
        }
      }

      // Merge LHS/RHS
      LHS = make_unique<BinaryExprAST>(Op, std::move(LHS), std::move(RHS));
    }
  }
};

// Code Generation Helper Class
class CodeGenerator {
public:
  static bool compileToObjectFile(Module &M, StringRef Filename) {
    // Initialize the native target and print processor
    string Error;
    auto TargetTriple = sys::getDefaultTargetTriple();

    const Target *TheTarget = TargetRegistry::lookupTarget(TargetTriple, Error);
    if (!TheTarget) {
      errs() << "Error looking up target: " << Error << '\n';
      return false;
    }

    // Set up target machine options
    TargetOptions Options;
    auto CPU = "generic";
    auto Features = "";

    TargetMachine *TargetMachine = TheTarget->createTargetMachine(
        TargetTriple, CPU, Features, Options, Reloc::PIC_, CodeModel::Small);

    // Set the module's data layout to match the target machine
    M.setDataLayout(TargetMachine->createDataLayout());
    M.setTargetTriple(TargetTriple);

    // Open the output file
    std::error_code EC;
    raw_fd_ostream Dest(Filename, EC, sys::fs::OF_None);

    if (EC) {
      errs() << "Could not open file: " << EC.message() << '\n';
      return false;
    }

    // Define the pass pipeline
    legacy::PassManager Pass;

    // Set the output file type
    auto FileType = LLVMObjectFile;

    // Add the target-specific passes to emit object file
    if (TargetMachine->addPassesToEmitFile(Pass, Dest, nullptr,
                                           llvm::CodeGenFileType(FileType))) {
      errs() << "TargetMachine can't emit a file of this type\n";
      return false;
    }

    // Run the passes
    Pass.run(M);
    Dest.flush();

    outs() << "Object code written to " << Filename << "\n";
    return true;
  }

  // Create a main function that calls user-defined functions with print
  // capability
  static void createMainFunction(Module &M) {
    // Declare printf and scanf functions for I/O
    FunctionType *printf_type = FunctionType::get(
        Type::getInt32Ty(*TheContext),
        PointerType::get(Type::getInt8Ty(*TheContext), 0), true);
    Function *printf_func =
        Function::Create(printf_type, Function::ExternalLinkage, "printf", &M);
    
    FunctionType *scanf_type = FunctionType::get(
        Type::getInt32Ty(*TheContext),
        PointerType::get(Type::getInt8Ty(*TheContext), 0), true);
    Function *scanf_func =
        Function::Create(scanf_type, Function::ExternalLinkage, "scanf", &M);
  
    // Create main function
    FunctionType *main_type = FunctionType::get(
        Type::getInt32Ty(*TheContext),
        {Type::getInt32Ty(*TheContext),
         PointerType::get(PointerType::get(Type::getInt8Ty(*TheContext), 0),
                          0)},
        false);
    Function *main_func =
        Function::Create(main_type, Function::ExternalLinkage, "main", &M);
  
    // Name the arguments (even though we won't use them)
    Function::arg_iterator args = main_func->arg_begin();
    Value *argc = args++;
    argc->setName("argc");
    Value *argv = args++;
    argv->setName("argv");
  
    // Create basic blocks
    BasicBlock *entry = BasicBlock::Create(*TheContext, "entry", main_func);
    BasicBlock *callFunctions =
        BasicBlock::Create(*TheContext, "call_functions", main_func);
  
    Builder->SetInsertPoint(entry);
  
    // Print header
    Value *HeaderStr =
        Builder->CreateGlobalStringPtr("--- Program Output ---\n", "header");
    Builder->CreateCall(printf_func, {HeaderStr}, "call_printf");
  
    // Create allocas for function parameters
    std::map<Function*, std::vector<AllocaInst*>> functionParamAllocas;
    
    // For each registered function, create allocas for its parameters
    for (auto &F : FunctionRegistry) {
      Function *function = F.second;
      std::vector<AllocaInst*> paramAllocas;
      
      unsigned paramIdx = 0;
      for (auto &param : function->args()) {
        std::string paramName = function->getName().str() + "_param" + std::to_string(paramIdx++);
        AllocaInst *paramAlloca = Builder->CreateAlloca(
            Type::getDoubleTy(*TheContext), nullptr, paramName);
        paramAllocas.push_back(paramAlloca);
      }
      
      functionParamAllocas[function] = paramAllocas;
    }
    
    // For each function, prompt and read dynamic input for parameters
    for (auto &F : FunctionRegistry) {
      Function *function = F.second;
      auto &paramAllocas = functionParamAllocas[function];
      
      unsigned paramCount = function->arg_size();
      
      // Create parameter names for better prompts
      std::vector<std::string> paramNames;
      if (function->getName() == "foo") {
        // Hardcoded parameter names for foo function
        paramNames = {"x", "y"};
      } else {
        // Generic parameter names for other functions
        for (unsigned i = 0; i < paramCount; i++) {
          paramNames.push_back("param" + std::to_string(i+1));
        }
      }
      
      // Display function information
      Value *FunctionInfoStr = Builder->CreateGlobalStringPtr(
          "Function " + function->getName().str() + " requires parameters:\n", 
          "function_info");
      Builder->CreateCall(printf_func, {FunctionInfoStr}, "call_info_printf");
      
      // Prompt for and read each parameter value
      for (unsigned i = 0; i < paramCount; i++) {
        // Create prompt for this parameter
        std::string promptStr = "Enter value for " + paramNames[i] + ": ";
        Value *PromptStr = Builder->CreateGlobalStringPtr(promptStr, "prompt_" + std::to_string(i));
        Builder->CreateCall(printf_func, {PromptStr}, "call_prompt_" + std::to_string(i));
        
        // Create format string for scanf
        Value *ScanfFormat = Builder->CreateGlobalStringPtr("%lf", "scanf_format_" + std::to_string(i));
        
        // Call scanf to read the value directly into the parameter alloca
        Builder->CreateCall(scanf_func, 
                          {ScanfFormat, 
                           Builder->CreateBitCast(paramAllocas[i], 
                                                  PointerType::get(Type::getInt8Ty(*TheContext), 0))},
                           "call_scanf_" + std::to_string(i));
      }
    }
    
    Builder->CreateBr(callFunctions);
    
    // Call functions block
    Builder->SetInsertPoint(callFunctions);
  
    // Call registered functions with parameters
    for (auto &F : FunctionRegistry) {
      std::string functionName = F.first;
      Function *function = F.second;
      auto &paramAllocas = functionParamAllocas[function];
      
      unsigned paramCount = function->arg_size();
      
      // Load parameters
      std::vector<Value*> paramValues;
      std::vector<Value*> printfArgValues;
      
      std::string formatStr = functionName + "(";
      for (unsigned i = 0; i < paramCount; i++) {
        Value *paramValue = Builder->CreateLoad(
            Type::getDoubleTy(*TheContext), paramAllocas[i], 
            "param_value_" + std::to_string(i));
        paramValues.push_back(paramValue);
        printfArgValues.push_back(paramValue);
        
        formatStr += "%f";
        if (i < paramCount - 1) {
          formatStr += ", ";
        }
      }
      formatStr += ") = %f\n";
      
      // Call the function
      Value *Result = Builder->CreateCall(function, paramValues, "call_result");
      
      // Create format string and print results
      Value *FormatStrPtr = Builder->CreateGlobalStringPtr(formatStr.c_str(), "format");
      
      // Add result to printf args
      printfArgValues.insert(printfArgValues.begin(), FormatStrPtr);
      printfArgValues.push_back(Result);
      
      Builder->CreateCall(printf_func, printfArgValues, "call_printf_result");
    }
  
    // Print footer
    Value *FooterStr =
        Builder->CreateGlobalStringPtr("--- End Output ---\n", "footer");
    Builder->CreateCall(printf_func, {FooterStr}, "call_printf_footer");
  
    // Return 0
    Builder->CreateRet(ConstantInt::get(Type::getInt32Ty(*TheContext), 0));
  }
  static bool linkToExecutable(StringRef ObjectFile, StringRef OutputFile) {
    // Use system call to invoke the C compiler for linking
    string Command = "gcc " + ObjectFile.str() + " -o " + OutputFile.str();

    outs() << "Linking with command: " << Command << "\n";

    int Result = system(Command.c_str());
    if (Result != 0) {
      errs() << "Linking failed with error code: " << Result << "\n";
      return false;
    }

    outs() << "Successfully linked executable: " << OutputFile << "\n";
    return true;
  }

  // Function to run the executable
  static void runExecutable(StringRef ExecutablePath) {
    outs() << "Running the compiled program...\n";

    string Command = "./" + ExecutablePath.str();
    system(Command.c_str());
  }
};

// Main
int main() {
  // Initialize LLVM target infrastructure
  InitializeNativeTarget();
  InitializeNativeTargetAsmPrinter();
  InitializeNativeTargetAsmParser();

  // Register all targets
  InitializeAllTargetInfos();
  InitializeAllTargets();
  InitializeAllTargetMCs();
  InitializeAllAsmParsers();
  InitializeAllAsmPrinters();

  // Create LLVM context and module
  TheContext = make_unique<LLVMContext>();
  TheModule = make_unique<Module>("my compiler", *TheContext);
  Builder = make_unique<IRBuilder<>>(*TheContext);

  // Read input file
  auto Buffer = MemoryBuffer::getFile("input.txt");
  if (!Buffer) {
    errs() << "Failed to read file\n";
    return 1;
  }

  // Lexical analysis
  StringRef Source = (*Buffer)->getBuffer();
  Lexer lexer(Source);
  auto tokens = lexer.tokenize();

  // Print tokens for debugging
  errs() << "Tokens:\n";
  for (const auto &token : tokens) {
    if (token.type != TokenType::EndOfFile)
      errs() << "  Type: " << static_cast<int>(token.type) << ", Value: '"
             << token.value << "'\n";
  }

  // Parse and generate IR
  Parser parser(tokens);
  parser.parseTopLevel();

  // Print the generated LLVM IR
  outs() << "Generated LLVM IR:\n";
  TheModule->print(outs(), nullptr);

  // Create a main function that calls our compiled functions
  CodeGenerator::createMainFunction(*TheModule);

  // Verify the module
  outs() << "Verifying module...\n";
  bool broken = verifyModule(*TheModule, &errs());
  if (broken) {
    errs() << "Module verification failed!\n";
    return 1;
  }

  // Compile to object file
  outs() << "Compiling to object code...\n";
  if (!CodeGenerator::compileToObjectFile(*TheModule, "output.o")) {
    errs() << "Failed to generate object code!\n";
    return 1;
  }

  // Link object file to executable
  if (!CodeGenerator::linkToExecutable("output.o", "program")) {
    errs() << "Failed to link executable!\n";
    return 1;
  }

  // Run the compiled program
  CodeGenerator::runExecutable("program");

  return 0;
}
