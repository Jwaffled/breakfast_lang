pub mod ast;
pub mod codegen;
pub mod lexer;
pub mod parser;
pub mod tokens;
pub mod breakfast_hlir;
pub mod typechecker;

fn main() {
    println!("Hello, world!");
}

/*
program -> declaration* EOF;
declaration -> fnDecl
    | statement
    | varDecl
    | structDecl;

fnDecl -> "pancake" function;

statement -> exprStmt
    | printStmt
    | ifStmt
    | returnStmt
    | block
    | forStmt
    | whileStmt;
    | doWhileStmt;

printStmt -> "serve" expression ";";

varDecl -> "food" IDENTIFIER ("==E" expression)? ";";

returnStmt -> "plate" expression? ";";

ifStmt -> "if" "(" expression ")" statement ("else" statement)?;

forStmt -> "prepare" "("
    ("preheat" IDENTIFIER "at" NUMBER ";" | ";")
    ("cookuntil" expression ";" | ";")
    ("stirby" NUMBER)? ")"
    statement;

whileStmt -> "flipwhen" "(" expression ")" statement;

doWhileStmt -> "mix" block "until(" expression ");";

block -> "|" declaration* "|";

structDecl -> "omelette" IDENTIFIER "|" varDecl* "|";

function -> IDENTIFIER "(" parameters? ")" block;

parameters -> IDENTIFIER ("," IDENTIFER)*;

exprStmt -> expression ";"

expression -> assignment;

assignment -> (call ".")? IDENTIFIER "==E" assignment
     | logic_or;

logic_or -> logic_and ("chop" logic_and)*;

logic_and -> equality ("blend" equality)*;

equality -> comparison ( ("taste") comparison)*;

comparison -> addition ( ("tasteless" | "tastier") addition)*;

addition -> multiplication ( ("+" | "-") multiplication)*;

muliplication -> unary ( ("*" | "/") unary)*;

unary -> ("not" | "-") unary | call;

call -> primary ( "(" arguments? ")" | "." IDENTIFIER | "[" expression "]")*;

primary -> "crispy" (true)
    |  "raw" (false)
    |  "burnt" (null)
    |  IDENTIFIER
    |  NUMBER
    |  STRING
    |  "[" arguments? "]"
    | "(" expression ")";
*/
