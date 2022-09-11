use std::fmt::Debug;
use std::fmt::Formatter;

use crate::ast::{
    BinaryOp, BinaryOpType, Expr, FunDecl, Literal, LogicalOpType, SourceLocation, Stmt,
    StructDecl, Symbol, TypeAnnotation, UnaryOp, UnaryOpType,
};
use crate::tokens;
use crate::tokens::{Token, TokenType};

pub fn parse(tokens: Vec<Token>) -> Result<Vec<Stmt>, ParserError> {
    let mut parser = Parser::new(tokens);
    parser.parse()
}

pub enum ParserError {
    UnexpectedToken(Token),
    InvalidSyntax {
        message: String,
        line: usize,
        col: i64,
    },
    TokenMismatch {
        expected: TokenType,
        found: Token,
        on_error: Option<String>,
    },
    MaxParamsExceeded {
        line: usize,
        col: i64,
    },
    ReturnNotInFunction {
        line: usize,
        col: i64,
    },
    InvalidAssignment {
        line: usize,
        col: i64,
    },
    TooManyArguments {
        line: usize,
        col: i64,
    },
    ExpectedExpression {
        token_type: TokenType,
        line: usize,
        col: i64,
    },
    InvalidTokenInUnaryOp {
        token_type: TokenType,
        line: usize,
        col: i64,
    },
    InvalidTokenInBinaryOp {
        token_type: TokenType,
        line: usize,
        col: i64,
    },
    ExpectedTypeToken {
        line: usize,
        col: i64,
    },
}

impl Debug for ParserError {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        match &self {
            Self::UnexpectedToken(token) => {
                write!(
                    f,
                    "Unexpected token {:?} on line {} col {}",
                    token, token.line, token.col
                )?;
            }
            Self::TokenMismatch {
                expected,
                found,
                on_error,
            } => {
                write!(
                    f,
                    "Expected token {:?} but found {:?} on line {} col {}",
                    expected, found, found.line, found.col
                )?;
                if let Some(on_error) = on_error {
                    write!(f, ": {}", on_error)?;
                }
            }
            Self::MaxParamsExceeded { line, col } => {
                write!(
                    f,
                    "Max parameters (255) exceeded for function on line {} col {}",
                    line, col
                )?;
            }
            Self::ReturnNotInFunction { line, col } => {
                write!(
                    f,
                    "Return statement with no enclosing function on line {} col {}",
                    line, col
                )?;
            }
            Self::InvalidAssignment { line, col } => {
                write!(f, "Invalid assignment target on line {} col {}", line, col)?;
            }
            Self::TooManyArguments { line, col } => {
                write!(
                    f,
                    "Cannot have more than 255 parameters to a single function on line {} col {}",
                    line, col
                )?;
            }
            Self::ExpectedExpression {
                token_type,
                line,
                col,
            } => {
                write!(
                    f,
                    "Expected expression but found {:?} on line {} col {}",
                    token_type, line, col
                )?;
            }
            Self::InvalidTokenInUnaryOp {
                token_type,
                line,
                col,
            } => {
                write!(
                    f,
                    "Invalid token {:?} in unary operation on line {} col {}",
                    token_type, line, col
                )?;
            }
            Self::InvalidTokenInBinaryOp {
                token_type,
                line,
                col,
            } => {
                write!(
                    f,
                    "Invalid token {:?} in binary operation on line {} col {}",
                    token_type, line, col
                )?;
            }

            Self::InvalidSyntax { message, line, col } => {
                write!(
                    f,
                    "Invalid syntax: {} on line {} col {}",
                    message, line, col
                )?;
            }
            Self::ExpectedTypeToken { line, col } => {
                write!(f, "Expected a type name on line {} col {}", line, col)?;
            }
        }

        Ok(())
    }
}

type FnArgument = (
    /* Variable name */ Symbol,
    /* Type argument */ TypeAnnotation,
);

pub struct Parser {
    tokens: Vec<Token>,
    current: usize,
    in_function: bool,
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

impl Parser {
    pub fn new(tokens: Vec<Token>) -> Self {
        Parser {
            tokens,
            current: 0,
            in_function: false,
        }
    }

    pub fn parse(&mut self) -> Result<Vec<Stmt>, ParserError> {
        let mut statements = Vec::new();

        while !self.is_at_end() {
            statements.push(self.declaration()?);
        }

        Ok(statements)
    }

    fn declaration(&mut self) -> Result<Stmt, ParserError> {
        /*
            declaration -> fnDecl
            | statement
            | varDecl
            | structDecl;
        */
        if self.match_token(TokenType::FunctionPancake) {
            return Ok(Stmt::FunDecl(self.fun_decl()?));
        }

        if self.match_token(TokenType::VarFood) {
            return self.var_decl();
        }

        if self.match_token(TokenType::StructOmelette) {
            return self.struct_decl();
        }

        self.statement()
    }

    fn fun_decl(&mut self) -> Result<FunDecl, ParserError> {
        let name = self.consume(
            TokenType::Identifier,
            "Expected function name after 'pancake' keyword",
        )?;

        let func_symbol = Symbol {
            name: name.lexeme.clone(),
            line: name.line,
            col: name.col,
        };

        let (params, body, ret_ty) = self.fun_params_and_body()?;

        Ok(FunDecl {
            name: func_symbol,
            params,
            body,
            ret_ty,
        })
    }

    fn fun_params_and_ret(&mut self) -> Result<(Vec<FnArgument>, TypeAnnotation), ParserError> {
        self.consume(
            TokenType::LeftParen,
            "Expected '(' after function declaration",
        )?;

        let mut params = Vec::new();

        if !self.check(TokenType::RightParen) {
            loop {
                if params.len() >= 255 {
                    return Err(ParserError::TooManyArguments {
                        line: self.get_current().line,
                        col: self.get_current().col,
                    });
                }

                let param = self
                    .consume(
                        TokenType::Identifier,
                        "Expected parameter name in function declaration",
                    )?
                    .clone();

                self.consume(TokenType::Colon, "Expected ':' to type parameter")?;

                let param_ty = self.consume_type_annotation()?;

                params.push((
                    Symbol {
                        name: param.lexeme,
                        line: param.line,
                        col: param.col,
                    },
                    param_ty,
                ));

                if !self.match_token(TokenType::Comma) {
                    break;
                }
            }
        }

        self.consume(
            TokenType::RightParen,
            "Expected ')' after function parameters",
        )?;

        self.consume(TokenType::Colon, "Expected ':' for function return type")?;

        let ret_ty = self.consume_type_annotation()?;
        Ok((params, ret_ty))
    }

    fn fun_params_and_body(
        &mut self,
    ) -> Result<(Vec<FnArgument>, Vec<Stmt>, TypeAnnotation), ParserError> {
        let (params, ret_ty) = self.fun_params_and_ret()?;

        self.consume(
            TokenType::OpenScopeBar,
            "Expected '|>' before function body",
        )?;

        self.in_function = true;
        let body = self.block()?;
        self.in_function = false;
        Ok((params, body, ret_ty))
    }

    fn struct_decl(&mut self) -> Result<Stmt, ParserError> {
        let name_tok = self
            .consume(TokenType::Identifier, "Expected struct name")?
            .clone();

        let struct_symbol = Symbol {
            name: name_tok.lexeme,
            line: name_tok.line,
            col: name_tok.col,
        };

        self.consume(TokenType::OpenScopeBar, "Expected '|>' before struct body")?;

        let mut fields = Vec::new();
        while !self.check(TokenType::CloseScopeBar) && !self.is_at_end() {
            fields.push(self.var_decl()?);
        }
        let fields = fields;

        self.consume(TokenType::CloseScopeBar, "Expected '<|' after struct body")?;

        Ok(Stmt::StructDecl(StructDecl {
            name: struct_symbol,
            fields,
        }))
    }

    fn var_decl(&mut self) -> Result<Stmt, ParserError> {
        let name_tok = self
            .consume(TokenType::Identifier, "Expected variable name")?
            .clone();

        let maybe_type_ann = if self.match_token(TokenType::Colon) {
            let type_ann_token = self.consume_type_annotation()?;

            // TODO: Support parsing things like string[][][], create TypeAnnotation type in ast.rs

            Some(type_ann_token)
        } else {
            None
        };

        println!("type ann: {:?}", maybe_type_ann);

        let maybe_init = if self.match_token(TokenType::AssignFork) {
            Some(self.expression()?)
        } else {
            None
        };

        self.consume(
            TokenType::Semicolon,
            "Expected '#' after variable declaration",
        )?;

        Ok(Stmt::VarDecl(
            Symbol {
                name: name_tok.lexeme,
                line: name_tok.line,
                col: name_tok.col,
            },
            maybe_type_ann,
            maybe_init,
        ))
    }

    fn statement(&mut self) -> Result<Stmt, ParserError> {
        /*
            statement -> exprStmt
            | printStmt
            | ifStmt
            | returnStmt
            | block
            | forStmt
            | whileStmt;
            | doWhileStmt;
        */
        if self.match_token(TokenType::ForPrepare) {
            return self.for_stmt();
        }

        if self.match_token(TokenType::WhileFlipwhen) {
            return self.while_stmt();
        }

        if self.match_token(TokenType::If) {
            return self.if_stmt();
        }

        if self.match_token(TokenType::DoWhileMix) {
            return self.do_while_stmt();
        }

        if self.match_token(TokenType::OpenScopeBar) {
            return Ok(Stmt::Block(self.block()?));
        }

        if self.match_token(TokenType::ReturnPlate) {
            return self.return_stmt();
        }

        if self.match_token(TokenType::PrintServe) {
            return self.print_stmt();
        }

        self.expression_stmt()
    }

    fn for_stmt(&mut self) -> Result<Stmt, ParserError> {
        /*
            forStmt -> "prepare" "("
            ("preheat" IDENTIFIER "at" expression ";" | ";")
            ("cookuntil" expression ";" | ";")
            ("stirby" expression)? ")"
            statement;
        */
        self.consume(TokenType::LeftParen, "Expected '(' after 'prepare'")?;
        let maybe_init = if self.match_token(TokenType::ForPreheat) {
            let name_tok = self
                .consume(TokenType::Identifier, "Expected identifier after 'preheat'")?
                .clone();
            self.consume(TokenType::ForAt, "Expected 'at' after identifier")?;
            let value = self.expression()?;
            self.consume(TokenType::Semicolon, "Expected '#' after expression")?;
            Some(Stmt::VarDecl(
                Symbol {
                    name: name_tok.lexeme,
                    line: name_tok.line,
                    col: name_tok.col,
                },
                None,
                Some(value),
            ))
        } else {
            None
        };

        let maybe_cond = if !self.check(TokenType::Semicolon) {
            self.consume(
                TokenType::ForCookUntil,
                "Expected 'cookuntil' before loop condition",
            )?;
            Some(self.expression()?)
        } else {
            None
        };

        self.consume(TokenType::Semicolon, "Expected ';' after loop condition")?;

        let maybe_inc = if !self.check(TokenType::RightParen) {
            self.consume(TokenType::ForStir, "Expected 'stir' after loop condition")?;
            Some(self.expression()?)
        } else {
            None
        };

        self.consume(TokenType::RightParen, "Expected ')' after prepare clauses")?;

        let mut body = self.statement()?;

        if let Some(inc) = maybe_inc {
            body = Stmt::Block(vec![body, Stmt::Expr(inc)]);
        }

        let condition = match maybe_cond {
            Some(cond) => cond,
            None => Expr::Literal(Literal::True),
        };
        body = Stmt::While(condition, Box::new(body), false);

        if let Some(init) = maybe_init {
            body = Stmt::Block(vec![init, body])
        }
        let body = body;

        Ok(body)
    }

    fn while_stmt(&mut self) -> Result<Stmt, ParserError> {
        /*
            whileStmt -> "flipwhen" "(" expression ")" statement;
        */
        self.consume(TokenType::LeftParen, "Expected '(' after 'flipwhen'")?;
        let condition = self.expression()?;
        self.consume(TokenType::RightParen, "Expected ')' after condition")?;
        let body = Box::new(self.statement()?);

        Ok(Stmt::While(condition, body, false))
    }

    fn if_stmt(&mut self) -> Result<Stmt, ParserError> {
        /*
            ifStmt -> "if" "(" expression ")" statement ("else" statement)?;
        */
        self.consume(TokenType::LeftParen, "Expected '(' after 'if'")?;
        let condition = self.expression()?;
        self.consume(TokenType::RightParen, "Expected ')' after if condition")?;
        let then_branch = Box::new(self.statement()?);
        let else_branch = if self.match_token(TokenType::Else) {
            Some(Box::new(self.statement()?))
        } else {
            None
        };

        Ok(Stmt::If(condition, then_branch, else_branch))
    }

    fn do_while_stmt(&mut self) -> Result<Stmt, ParserError> {
        /*
        doWhileStmt -> "mix" statement "until(" expression ");";
        */
        // mix print 1 until(false);
        let body = self.statement()?;
        self.consume(TokenType::DoWhileUntil, "Expected 'until' after mix body")?;
        self.consume(TokenType::LeftParen, "Expected '(' after 'until'")?;
        let condition = self.expression()?;
        self.consume(
            TokenType::RightParen,
            "Expected ')' after 'until' condition",
        )?;
        self.consume(TokenType::Semicolon, "Expected ';' after 'until' condition")?;

        Ok(Stmt::While(condition, Box::new(body), true))
    }

    fn block(&mut self) -> Result<Vec<Stmt>, ParserError> {
        let mut statements = Vec::new();

        while !self.check(TokenType::CloseScopeBar) && !self.is_at_end() {
            statements.push(self.declaration()?);
        }

        self.consume(TokenType::CloseScopeBar, "Expected '<|' after block")?;

        Ok(statements)
    }

    fn return_stmt(&mut self) -> Result<Stmt, ParserError> {
        let prev_tok = self.previous().clone();

        if !self.in_function {
            return Err(ParserError::ReturnNotInFunction {
                line: prev_tok.line,
                col: prev_tok.col,
            });
        }

        let maybe_val = if !self.check(TokenType::Semicolon) {
            Some(self.expression()?)
        } else {
            None
        };

        if maybe_val.is_some() {
            self.consume(TokenType::Semicolon, "Expected '#' after return value.")?;
        }

        Ok(Stmt::Return(
            SourceLocation {
                line: prev_tok.line,
                col: prev_tok.col,
            },
            maybe_val,
        ))
    }

    fn print_stmt(&mut self) -> Result<Stmt, ParserError> {
        let value = self.expression()?;
        self.consume(TokenType::Semicolon, "Expected '#' after expression.")?;
        Ok(Stmt::Print(value))
    }

    fn expression_stmt(&mut self) -> Result<Stmt, ParserError> {
        let expr = self.expression()?;

        self.consume(
            TokenType::Semicolon,
            "Expected '#' after expression statement.",
        )?;

        Ok(Stmt::Expr(expr))
    }

    fn expression(&mut self) -> Result<Expr, ParserError> {
        self.assignment()
    }

    fn assignment(&mut self) -> Result<Expr, ParserError> {
        /*
           assignment -> (call ".")? IDENTIFIER "==E" assignment
        | logic_or;
           */
        let expr = self.logic_or()?;

        if self.match_token(TokenType::AssignFork) {
            let fork = self.previous().clone();
            let new_val = self.assignment()?;

            if let Expr::Variable(name) = &expr {
                return Ok(Expr::Assign(name.clone(), Box::new(new_val)));
            } else if let Expr::Get(e, attr) = expr {
                return Ok(Expr::Set(e, attr, Box::new(new_val)));
            } else {
                return Err(ParserError::InvalidAssignment {
                    line: fork.line,
                    col: fork.col,
                });
            }
        }

        Ok(expr)
    }

    fn logic_or(&mut self) -> Result<Expr, ParserError> {
        // logic_or -> logic_and ("chop" logic_and)*;
        let mut expr = self.logic_and()?;
        while self.match_token(TokenType::OrChop) {
            let right = self.logic_and()?;
            expr = Expr::Logical(Box::new(expr), LogicalOpType::OrChop, Box::new(right));
        }

        Ok(expr)
    }

    fn logic_and(&mut self) -> Result<Expr, ParserError> {
        // logic_and -> equality ("blend" equality)*;
        let mut expr = self.equality()?;
        while self.match_token(TokenType::AndBlend) {
            let right = self.equality()?;
            expr = Expr::Logical(Box::new(expr), LogicalOpType::AndBlend, Box::new(right));
        }

        Ok(expr)
    }

    fn equality(&mut self) -> Result<Expr, ParserError> {
        // equality -> comparison ( ("taste") comparison)*;
        let mut expr = self.comparison()?;
        while self.matches_one([TokenType::EqualEqualTaste]) {
            let operator = self.previous().clone(); // Not necessary, I just might add in a not equal operator later
            let right = self.comparison()?;
            let op_type = Parser::binary_op_type(&operator)?;
            expr = Expr::Binary(Box::new(expr), op_type, Box::new(right));
        }

        Ok(expr)
    }

    fn comparison(&mut self) -> Result<Expr, ParserError> {
        // comparison -> addition ( ("tasteless" | "tastier") addition)*;
        let mut expr = self.addition()?;
        while self.matches_one([TokenType::LessThanTasteless, TokenType::GreaterThanTastier]) {
            let operator = self.previous().clone();
            let right = self.addition()?;
            let op_type = Parser::binary_op_type(&operator)?;
            expr = Expr::Binary(Box::new(expr), op_type, Box::new(right));
        }

        Ok(expr)
    }

    fn addition(&mut self) -> Result<Expr, ParserError> {
        // addition -> multiplication ( ("+" | "-") multiplication)*;
        let mut expr = self.multiplication()?;
        while self.matches_one([TokenType::Plus, TokenType::Minus]) {
            let operator = self.previous().clone();
            let right = self.multiplication()?;
            let op_type = Parser::binary_op_type(&operator)?;
            expr = Expr::Binary(Box::new(expr), op_type, Box::new(right));
        }

        Ok(expr)
    }

    fn multiplication(&mut self) -> Result<Expr, ParserError> {
        // muliplication -> unary ( ("*" | "/") unary)*;
        let mut expr = self.unary()?;
        while self.matches_one([TokenType::Star, TokenType::Slash]) {
            let operator = self.previous().clone();
            let right = self.unary()?;
            let op_type = Parser::binary_op_type(&operator)?;
            expr = Expr::Binary(Box::new(expr), op_type, Box::new(right));
        }

        Ok(expr)
    }

    fn unary(&mut self) -> Result<Expr, ParserError> {
        // unary -> ("not" | "-") unary | call;
        if self.matches_one([TokenType::Not, TokenType::Minus]) {
            let operator = self.previous().clone();
            let right = self.unary()?;
            let op_type = Parser::unary_op_type(&operator)?;
            return Ok(Expr::Unary(op_type, Box::new(right)));
        }

        self.call()
    }

    fn call(&mut self) -> Result<Expr, ParserError> {
        // call -> primary ( "(" arguments? ")" | "." IDENTIFIER | "[" expression "]")*;
        let mut expr = self.primary()?;
        loop {
            if self.match_token(TokenType::LeftParen) {
                expr = self.finish_call(expr)?;
            } else if self.match_token(TokenType::Dot) {
                let name = self
                    .consume(TokenType::Identifier, "Expected field name after '.'")?
                    .clone();

                expr = Expr::Get(
                    Box::new(expr),
                    Symbol {
                        name: name.lexeme,
                        line: name.line,
                        col: name.col,
                    },
                );
            } else if self.match_token(TokenType::LeftBracket) {
                let slice_expr = self.expression()?;

                let token = self.consume(
                    TokenType::RightBracket,
                    "Expected ']' after array index expression.",
                )?;

                expr = Expr::Subscript {
                    value: Box::new(expr),
                    slice: Box::new(slice_expr),
                    source_location: SourceLocation {
                        line: token.line,
                        col: token.col,
                    },
                }
            } else {
                break;
            }
        }

        Ok(expr)
    }

    fn finish_call(&mut self, expr: Expr) -> Result<Expr, ParserError> {
        let mut arguments = Vec::new();

        if !self.check(TokenType::RightParen) {
            loop {
                if arguments.len() >= 255 {
                    return Err(ParserError::TooManyArguments {
                        line: self.get_current().line,
                        col: self.get_current().col,
                    });
                }

                arguments.push(self.expression()?);

                if !self.match_token(TokenType::Comma) {
                    break;
                }
            }
        }

        let paren = self.consume(
            TokenType::RightParen,
            "Expected ')' after arguments in function call.",
        )?;

        Ok(Expr::Call(
            Box::new(expr),
            SourceLocation {
                line: paren.line,
                col: paren.col,
            },
            arguments,
        ))
    }

    fn primary(&mut self) -> Result<Expr, ParserError> {
        /*
        primary -> "crispy" (true)
        |  "raw" (false)
        |  "burnt" (null)
        |  IDENTIFIER
        |  NUMBER
        |  STRING
        |  "[" arguments? "]"
        | "(" expression ")";
        */
        if self.match_token(TokenType::TrueCrispy) {
            return Ok(Expr::Literal(Literal::True));
        }

        if self.match_token(TokenType::FalseRaw) {
            return Ok(Expr::Literal(Literal::False));
        }

        if self.match_token(TokenType::NullBurnt) {
            return Ok(Expr::Literal(Literal::Null));
        }

        if self.match_token(TokenType::Number) {
            match &self.previous().literal {
                Some(tokens::Literal::Number(n)) => {
                    return Ok(Expr::Literal(Literal::Number(*n)));
                }
                Some(other) => {
                    panic!(
                        "Internal parser error: Expected number literal, got {:?}",
                        other
                    );
                }
                None => {
                    panic!("Internal parser error: Expected number literal, got None");
                }
            }
        }

        if self.match_token(TokenType::LeftParen) {
            let expr = self.expression()?;
            self.consume(
                TokenType::RightParen,
                "Expected ')' after grouping expression.",
            )?;
            return Ok(Expr::Grouping(Box::new(expr)));
        }

        if self.match_token(TokenType::String) {
            match &self.previous().literal {
                Some(tokens::Literal::String(s)) => {
                    return Ok(Expr::Literal(Literal::String(s.clone())));
                }
                Some(other) => {
                    panic!(
                        "Internal parser error: Expected string literal, got {:?}",
                        other
                    );
                }
                None => {
                    panic!("Internal parser error: Expected string literal, got None");
                }
            }
        }

        if self.match_token(TokenType::Identifier) {
            match &self.previous().literal {
                Some(tokens::Literal::Identifier(s)) => {
                    return Ok(Expr::Variable(Symbol {
                        name: s.clone(),
                        line: self.previous().line,
                        col: self.previous().col,
                    }));
                }
                Some(other) => {
                    panic!(
                        "Internal parser error: Expected identifier literal, got {:?}",
                        other
                    );
                }
                None => {
                    panic!("Internal parser error: Expected identifier literal, got None");
                }
            }
        }

        if self.match_token(TokenType::LeftBracket) {
            let mut elements = Vec::new();
            if !self.check(TokenType::RightBracket) {
                loop {
                    elements.push(self.expression()?);
                    if !self.match_token(TokenType::Comma) {
                        break;
                    }
                }
            }
            self.consume(
                TokenType::RightBracket,
                "Expected ']' after array elements.",
            )?;
            return Ok(Expr::List(elements));
        }

        Err(ParserError::ExpectedExpression {
            token_type: self.get_current().token_type,
            line: self.get_current().line,
            col: self.get_current().col,
        })
    }

    fn matches_one<Item: IntoIterator<Item = TokenType>>(&mut self, items: Item) -> bool {
        for item in items {
            if self.match_token(item) {
                return true;
            }
        }

        false
    }

    fn consume(&mut self, expected: TokenType, error_msg: &str) -> Result<&Token, ParserError> {
        if self.check(expected) {
            Ok(self.advance())
        } else {
            Err(ParserError::TokenMismatch {
                expected,
                found: self.get_current().clone(),
                on_error: Some(error_msg.to_string()),
            })
        }
    }

    fn consume_type(&mut self) -> Result<TypeAnnotation, ParserError> {
        let current = self.advance().clone();

        let matches = match current.token_type {
            TokenType::BoolTexture => Some(TypeAnnotation::Bool),
            TokenType::StringSmoothie => Some(TypeAnnotation::String),
            TokenType::NumberCal => Some(TypeAnnotation::Number),
            TokenType::VoidEmpty => Some(TypeAnnotation::Void),
            TokenType::FunctionPancake => {
                let (params, ret_ty) = self.fun_params_and_ret()?;
                let arg_tys = params.into_iter().map(|(_, ty)| ty).collect::<Vec<_>>();
                Some(TypeAnnotation::Function(None, arg_tys, Box::new(ret_ty)))
            }
            TokenType::Identifier => Some(TypeAnnotation::Struct(Symbol {
                name: current.lexeme,
                line: current.line,
                col: current.col,
            })),
            _ => None,
        };

        if let Some(ann) = matches {
            Ok(ann)
        } else {
            Err(ParserError::ExpectedTypeToken {
                line: current.line,
                col: current.col,
            })
        }
    }

    fn consume_type_annotation(&mut self) -> Result<TypeAnnotation, ParserError> {
        /*
        TypeAnn -> TypeAnn "[]"* | ident | "cal" | "smoothie" | "texture" | "empty" | "pancake" "(" arguments? "):" TypeAnn
        */
        let mut ty_tok = self.consume_type()?;

        while self.match_token(TokenType::LeftBracket) {
            if matches!(ty_tok, TypeAnnotation::Void) {
                let curr = self.get_current();
                return Err(ParserError::InvalidSyntax {
                    message: "Type 'empty' cannot be made into an array".to_string(),
                    line: curr.line,
                    col: curr.col,
                });
            }
            self.consume(
                TokenType::RightBracket,
                "Expected ']' following '[' in type annotation",
            )?;
            ty_tok = TypeAnnotation::Array(Box::new(ty_tok));
        }

        Ok(ty_tok)
    }

    fn previous(&self) -> &Token {
        &self.tokens[self.current - 1]
    }

    fn advance(&mut self) -> &Token {
        if !self.is_at_end() {
            self.current += 1;
        }

        self.previous()
    }

    fn match_token(&mut self, token_type: TokenType) -> bool {
        if self.is_at_end() {
            return false;
        }

        if self.get_current().token_type == token_type {
            self.advance();
            return true;
        }

        false
    }

    fn check(&self, token_type: TokenType) -> bool {
        if self.is_at_end() {
            return false;
        }

        self.get_current().token_type == token_type
    }

    fn get_current(&self) -> &Token {
        &self.tokens[self.current]
    }

    fn is_at_end(&self) -> bool {
        self.get_current().token_type == TokenType::Eof
    }

    fn unary_op_type(token: &Token) -> Result<UnaryOp, ParserError> {
        match token.token_type {
            TokenType::Minus => Ok(UnaryOp {
                op_type: UnaryOpType::Minus,
                line: token.line,
                col: token.col,
            }),
            TokenType::Not => Ok(UnaryOp {
                op_type: UnaryOpType::Not,
                line: token.line,
                col: token.col,
            }),
            _ => Err(ParserError::InvalidTokenInUnaryOp {
                token_type: token.token_type,
                line: token.line,
                col: token.col,
            }),
        }
    }

    fn binary_op_type(token: &Token) -> Result<BinaryOp, ParserError> {
        match token.token_type {
            TokenType::Plus => Ok(BinaryOp {
                op_type: BinaryOpType::Plus,
                line: token.line,
                col: token.col,
            }),
            TokenType::Minus => Ok(BinaryOp {
                op_type: BinaryOpType::Minus,
                line: token.line,
                col: token.col,
            }),
            TokenType::Star => Ok(BinaryOp {
                op_type: BinaryOpType::Star,
                line: token.line,
                col: token.col,
            }),
            TokenType::Slash => Ok(BinaryOp {
                op_type: BinaryOpType::Slash,
                line: token.line,
                col: token.col,
            }),
            TokenType::LessThanTasteless => Ok(BinaryOp {
                op_type: BinaryOpType::LessThanTasteless,
                line: token.line,
                col: token.col,
            }),
            TokenType::GreaterThanTastier => Ok(BinaryOp {
                op_type: BinaryOpType::GreaterThanTastier,
                line: token.line,
                col: token.col,
            }),
            TokenType::EqualEqualTaste => Ok(BinaryOp {
                op_type: BinaryOpType::EqualEqualTaste,
                line: token.line,
                col: token.col,
            }),
            _ => Err(ParserError::InvalidTokenInBinaryOp {
                token_type: token.token_type,
                line: token.line,
                col: token.col,
            }),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::lexer;
    use crate::parser;

    #[test]
    fn test() {
        match lexer::lex_tokens(
            r#"
            pancake fn(arg1: smoothie, arg2: pancake(arg1: cal): smoothie): smoothie[][] |> <|
            pancake anotherFn(arg1: cal): smoothie |> plate "test" # <|
            fn("hi", anotherFn)#
            "#
            .to_string(),
        ) {
            Ok(tokens) => {
                let mut parser = parser::Parser::new(tokens);
                match parser.parse() {
                    Ok(stmts) => {
                        for stmt in stmts {
                            println!("{:#?}", stmt);
                        }
                        panic!()
                    }
                    Err(e) => {
                        panic!("Parser error: {:?}", e);
                    }
                }
            }
            Err(err) => {
                panic!("Lexer error: {}", err.message)
            }
        }
    }
}
