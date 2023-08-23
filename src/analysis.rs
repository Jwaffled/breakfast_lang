use std::{collections::HashMap, hash::Hash};

use crate::ast::{
    BinaryOp, BinaryOpType, Expr, FunDecl, Literal, SourceLocation, Stmt, StructDecl, Symbol,
    UnaryOp, UnaryOpType,
};

#[derive(Clone, Debug)]
enum Value {
    Number(f64),
    String(String),
    Null,
    Bool(bool),
    Struct(Symbol, u64),
    Instance(Symbol, u64),
    Function(Symbol, u64, Option<Box<Value>>),
}

// enum LookupResult<'a> {
//     Ok(&'a Typed<Value>),
//     UndefButDeclared(SourceLocation),
//     UndefAndUndeclared,
// }

// #[derive(Debug)]
// struct SymbolTable {
//     symbols: HashMap<String, (Option<Typed<Value>>, SourceLocation)>,
//     parent: Option<Box<SymbolTable>>,
// }

// impl SymbolTable {
//     pub fn new() -> Self {
//         SymbolTable {
//             parent: None,
//             symbols: HashMap::new(),
//         }
//     }
//     pub fn with_enclosing(enclosing: SymbolTable) -> Self {
//         SymbolTable {
//             parent: Some(Box::new(enclosing)),
//             symbols: HashMap::new(),
//         }
//     }

//     pub fn define(&mut self, symbol: Symbol, val: Option<Typed<Value>>) {
//         self.symbols.insert(
//             symbol.name,
//             (
//                 val,
//                 SourceLocation {
//                     line: symbol.line,
//                     col: symbol.col,
//                 },
//             ),
//         );
//     }

//     pub fn lookup(&self, symbol: &Symbol) -> LookupResult {
//         match self.symbols.get(&symbol.name) {
//             Some((val, source)) => match val {
//                 Some(value) => LookupResult::Ok(value),
//                 None => LookupResult::UndefButDeclared(SourceLocation {
//                     line: source.line,
//                     col: source.col,
//                 }),
//             },
//             None => LookupResult::UndefAndUndeclared,
//         }
//     }

//     pub fn get(&self, symbol: &Symbol) -> Result<&Typed<Value>, String> {
//         match self.lookup(symbol) {
//             LookupResult::Ok(val) => Ok(val),
//             LookupResult::UndefButDeclared(location) => Err(format!(
//                 "Use of undefined variable '{}' at line {} col {}.\
//                 \n'{}' was previously declared on line {} col {}, but was never defined.",
//                 &symbol.name, symbol.line, symbol.col, &symbol.name, location.line, location.col
//             )),
//             LookupResult::UndefAndUndeclared => match &self.parent {
//                 Some(enclosing) => enclosing.get(symbol),
//                 None => Err(format!(
//                     "Use of undefined variable '{}' on line {} col {}",
//                     &symbol.name, symbol.line, symbol.col
//                 )),
//             },
//         }
//     }

//     pub fn assign(&mut self, symbol: Symbol, value: &Typed<Value>) -> Result<(), String> {
//         if self.symbols.contains_key(&symbol.name) {
//             self.define(symbol, Some(value.clone()));
//             return Ok(());
//         }

//         match &mut self.parent {
//             Some(enclosing) => enclosing.assign(symbol, value),
//             None => Err(format!(
//                 "Attempting to assign to undeclared variable on line {} col {}",
//                 symbol.line, symbol.col
//             )),
//         }
//     }
// }

type TypeId = usize;

#[derive(Debug, Eq, PartialEq, Clone)]
enum TypeInfo {
    Number,
    String,
    Bool,
    Null,
    Void,
    Struct(TypeId),
    Function(TypeId, Vec<TypeId>),
    Array(TypeId),
}

enum TypeError {
    StructAlreadyDefined(SourceLocation),
    FunctionAlreadyDefined(SourceLocation),
    InvalidBinaryOp(SourceLocation, String),
    InvalidUnaryOp(SourceLocation, String),
    InvalidTypeName(SourceLocation, String),
    NoTypeInfo(SourceLocation, String),
}

impl std::fmt::Debug for TypeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::StructAlreadyDefined(loc) => write!(
                f,
                "TypeError: Duplicate struct definition on line {} col {}",
                loc.line, loc.col
            ),
            Self::FunctionAlreadyDefined(loc) => write!(
                f,
                "TypeError: Duplicate function definition on line {} col {}",
                loc.line, loc.col
            ),
            Self::InvalidBinaryOp(loc, message) => write!(
                f,
                "TypeError: Invalid binary operation on line {} col {}: {}",
                loc.line, loc.col, message
            ),
            Self::InvalidUnaryOp(loc, message) => write!(
                f,
                "TypeError: Invalid unary operation on line {} col {}: {}",
                loc.line, loc.col, message
            ),
            Self::InvalidTypeName(loc, message) => write!(
                f,
                "TypeError: Type name nonexistent on line {} col {}: {}",
                loc.line, loc.col, message
            ),
            Self::NoTypeInfo(loc, message) => write!(
                f,
                "TypeError: No type information supplied on line {} col {}: {}",
                loc.line, loc.col, message
            ),
        }
    }
}

#[derive(Debug, Clone)]
struct Typed<T: Clone> {
    value: T,
    ty: TypeInfo,
}

impl<T: Clone> Typed<T> {
    pub fn new(ty: TypeInfo, value: T) -> Self {
        Self { ty, value }
    }
}

struct SymbolTable {
    symbols: HashMap<String, usize>,
    next_id: usize,
}

impl SymbolTable {
    fn new() -> Self {
        Self {
            symbols: HashMap::new(),
            next_id: 0,
        }
    }

    fn get_or_intern(&mut self, symbol: &str) -> usize {
        if let Some(&id) = self.symbols.get(symbol) {
            id
        } else {
            self.symbols.insert(symbol.to_string(), self.next_id);
            let saved = self.next_id;
            self.next_id += 1;
            saved
        }
    }
}

type TypedAST = Vec<Typed<Stmt>>;

struct TypeBuilder {
    symbol_table: SymbolTable
}

impl TypeBuilder {
    pub fn new() -> Self {
        Self {
            symbol_table: SymbolTable::new()
        }
    }

    pub fn build(&mut self, ast: Vec<Stmt>) -> Result<TypedAST, TypeError> {
        self.resolve_all(&ast);
        ast.into_iter()
            .map(|node| self.build_stmt(node))
            .collect::<Result<TypedAST, TypeError>>()
    }

    fn build_stmt(&mut self, stmt: Stmt) -> Result<Typed<Stmt>, TypeError> {}

    fn resolve_all(&mut self, ast: &[Stmt]) -> Result<(), TypeError> {
        for node in ast {
            match node {
                Stmt::StructDecl(struct_decl) => {
                    let id = self.symbol_table.get_or_intern(&struct_decl.name.name);
                    
                }

                Stmt::FunDecl(fun_decl) => {}

                Stmt::VarDecl(symbol, maybe_type, maybe_init) => {}

                _ => {}
            }
        }

        Ok(())
    }
}

// /* TODO
//  *  - Intern idents
//  *  - Resolve structs and functions to DefIds
//  *  -
//  */
// #[derive(Debug)]
// struct TypeBuilder {
//     structs: HashMap<String, TypeId>,
//     functions: HashMap<String, (TypeId, TypeId)>, // (FuncId, ReturnTypeId)
//     struct_decls: Vec<StructDecl>,
//     func_decls: Vec<FunDecl>,
//     struct_counter: usize,
//     func_counter: usize,
//     symbol_table: SymbolTable,
// }

// impl TypeBuilder {
//     pub fn new() -> Self {
//         let mut type_decls = Vec::new();
//         let mut type_ids = HashMap::new();
//         type_ids.insert("number".to_string(), 0usize);
//         type_decls.push(StructDecl::create_native("number".to_string()));

//         type_ids.insert("string".to_string(), 1);
//         type_decls.push(StructDecl::create_native("string".to_string()));

//         type_ids.insert("bool".to_string(), 2);
//         type_decls.push(StructDecl::create_native("bool".to_string()));

//         type_ids.insert("void".to_string(), 3);
//         type_decls.push(StructDecl::create_native("void".to_string()));

//         TypeBuilder {
//             structs: type_ids,
//             functions: HashMap::new(),
//             struct_counter: type_decls.len(),
//             struct_decls: type_decls,
//             func_decls: Vec::new(),
//             func_counter: 0,
//             symbol_table: SymbolTable::new(),
//         }
//     }

//     pub fn build(&mut self, ast: Vec<Stmt>) -> Result<Vec<Typed<Stmt>>, TypeError> {
//         self.register_structs_and_fns(&ast)?;
//         let typed_ast = ast
//             .into_iter()
//             .map(|node| self.build_stmt(node))
//             .collect::<Result<Vec<_>, _>>()?;
//         Ok(typed_ast)
//     }

//     fn build_stmt(&mut self, stmt: Stmt) -> Result<Typed<Stmt>, TypeError> {
//         match stmt {
//             Stmt::Expr(expr) => {
//                 let expr = self.build_expr(expr)?;
//                 Ok(Typed::new(expr.ty, Stmt::Expr(expr.value)))
//             }
//             Stmt::VarDecl(name, maybe_ty, maybe_init) => {
//                 if maybe_ty.is_none() && maybe_init.is_none() {
//                     Err(TypeError::NoTypeInfo(SourceLocation { line: name.line, col: name.col }, "Either an initializer expression or type annotation must be supplied when declaring variables!".to_string()))
//                 } else {
//                     if let Some(init) = maybe_init {
//                         let initty = self.build_expr(init)?;
//                         if let Some(ty) = maybe_ty {
//                             // Check if types agree

//                             todo!()
//                         } else {
//                             // Infer
//                             todo!()
//                         }
//                     } else {
//                         // Type annotation only with no init
//                         todo!()
//                     }
//                 }
//             }
//             _ => todo!(),
//         }
//     }

//     fn build_expr(&mut self, expr: Expr) -> Result<Typed<Expr>, TypeError> {
//         match expr {
//             Expr::Literal(literal) => {
//                 let ty = self.build_literal(literal);
//                 Ok(Typed::new(ty.ty, Expr::Literal(ty.value)))
//             }
//             Expr::Binary(lhs, op, rhs) => self.build_binary(lhs, op, rhs),
//             Expr::Unary(op, expr) => self.build_unary(expr, op),
//             _ => todo!(),
//         }
//     }

//     fn build_unary(&mut self, expr: Box<Expr>, op: UnaryOp) -> Result<Typed<Expr>, TypeError> {
//         let exprty = self.build_expr(*expr.clone())?;

//         match (exprty.ty, op.op_type) {
//             (TypeInfo::Bool, UnaryOpType::Not) => {
//                 Ok(Typed::new(TypeInfo::Bool, Expr::Unary(op, expr)))
//             }
//             (TypeInfo::Number, UnaryOpType::Minus) => {
//                 Ok(Typed::new(TypeInfo::Number, Expr::Unary(op, expr)))
//             }
//             (ty, _) => Err(TypeError::InvalidUnaryOp(
//                 SourceLocation {
//                     line: op.line,
//                     col: op.col,
//                 },
//                 format!(
//                     "Cannot use unary operator '{}' on type '{}'",
//                     op,
//                     self.pretty_ty(ty)
//                 ),
//             )),
//         }
//     }

//     fn build_binary(
//         &mut self,
//         lhs: Box<Expr>,
//         op: BinaryOp,
//         rhs: Box<Expr>,
//     ) -> Result<Typed<Expr>, TypeError> {
//         let lhsty = self.build_expr(*lhs.clone())?;
//         let rhsty = self.build_expr(*rhs.clone())?;

//         match (lhsty.ty, rhsty.ty) {
//             (TypeInfo::Number, TypeInfo::Number) => match op.op_type {
//                 BinaryOpType::Star
//                 | BinaryOpType::Minus
//                 | BinaryOpType::Slash
//                 | BinaryOpType::Plus => {
//                     Ok(Typed::new(TypeInfo::Number, Expr::Binary(lhs, op, rhs)))
//                 }
//                 BinaryOpType::EqualEqualTaste
//                 | BinaryOpType::GreaterThanTastier
//                 | BinaryOpType::LessThanTasteless => {
//                     Ok(Typed::new(TypeInfo::Bool, Expr::Binary(lhs, op, rhs)))
//                 }
//             },
//             (TypeInfo::Bool, TypeInfo::Bool) => match op.op_type {
//                 BinaryOpType::EqualEqualTaste => {
//                     Ok(Typed::new(TypeInfo::Bool, Expr::Binary(lhs, op, rhs)))
//                 }
//                 _ => Err(TypeError::InvalidBinaryOp(
//                     SourceLocation {
//                         line: op.line,
//                         col: op.col,
//                     },
//                     format!("Cannot use binary operator '{}' on booleans", op),
//                 )),
//             },
//             (TypeInfo::String, TypeInfo::String) => match op.op_type {
//                 BinaryOpType::Plus | BinaryOpType::EqualEqualTaste => {
//                     Ok(Typed::new(TypeInfo::String, Expr::Binary(lhs, op, rhs)))
//                 }
//                 _ => Err(TypeError::InvalidBinaryOp(
//                     SourceLocation {
//                         line: op.line,
//                         col: op.col,
//                     },
//                     format!("Cannot use binary operator '{}' on strings", op),
//                 )),
//             },
//             (TypeInfo::Array(ty), other) => match op.op_type {
//                 BinaryOpType::Plus => {
//                     if *ty == other {
//                         Ok(Typed::new(TypeInfo::Array(ty), Expr::Binary(lhs, op, rhs)))
//                     } else {
//                         Err(TypeError::InvalidBinaryOp(
//                             SourceLocation {
//                                 line: op.line,
//                                 col: op.col,
//                             },
//                             format!(
//                                 "Cannot use binary operator '{}' on types '{}' and '{}'",
//                                 op,
//                                 self.pretty_ty(*ty),
//                                 self.pretty_ty(other)
//                             ),
//                         ))
//                     }
//                 }
//                 _ => Err(TypeError::InvalidBinaryOp(
//                     SourceLocation {
//                         line: op.line,
//                         col: op.col,
//                     },
//                     format!("Cannot use binary operator '{}' on Arrays", op),
//                 )),
//             },
//             (lhs, rhs) => Err(TypeError::InvalidBinaryOp(
//                 SourceLocation {
//                     line: op.line,
//                     col: op.col,
//                 },
//                 format!(
//                     "Cannot use binary operator '{}' on types '{}' and '{}'",
//                     op,
//                     self.pretty_ty(lhs),
//                     self.pretty_ty(rhs)
//                 ),
//             )),
//         }
//     }

//     fn build_literal(&mut self, literal: Literal) -> Typed<Literal> {
//         match literal {
//             Literal::False | Literal::True => Typed::new(TypeInfo::Bool, literal),
//             Literal::Null => Typed::new(TypeInfo::Null, literal),
//             Literal::Number(_) => Typed::new(TypeInfo::Number, literal),
//             Literal::String(_) => Typed::new(TypeInfo::String, literal),
//         }
//     }

//     fn types_match(&self, ty1: &TypeInfo, ty2: &TypeInfo) -> bool {
//         ty1 == ty2
//     }

//     fn get_func(&self, name: String) -> Option<(TypeId, TypeId)> {
//         self.functions.get(&name).cloned()
//     }

//     fn get_struct(&self, name: String) -> Option<TypeId> {
//         self.structs.get(&name).cloned()
//     }

//     fn alloc_struct_id(&mut self) -> TypeId {
//         let id = self.struct_counter;
//         self.struct_counter += 1;
//         id
//     }

//     fn alloc_fn_id(&mut self) -> TypeId {
//         let id = self.func_counter;
//         self.func_counter += 1;
//         id
//     }

//     fn register_structs_and_fns(&mut self, ast: &[Stmt]) -> Result<(), TypeError> {
//         for node in ast {
//             match node {
//                 Stmt::StructDecl(decl) => {
//                     if self.structs.contains_key(&decl.name.name) {
//                         return Err(TypeError::StructAlreadyDefined(SourceLocation {
//                             line: decl.name.line,
//                             col: decl.name.col,
//                         }));
//                     } else {
//                         let id = self.alloc_struct_id();
//                         self.structs.insert(decl.name.name.clone(), id);
//                         self.struct_decls.push(decl.clone());
//                     }
//                 }
//                 Stmt::FunDecl(decl) => {
//                     if self.functions.contains_key(&decl.name.name) {
//                         return Err(TypeError::FunctionAlreadyDefined(SourceLocation {
//                             line: decl.name.line,
//                             col: decl.name.col,
//                         }));
//                     }

//                     // if let Some(ret_ty) = self.get_struct(decl.ret_ty.name.clone()) {
//                     //     let id = self.alloc_fn_id();
//                     //     self.functions.insert(decl.name.name.clone(), (id, ret_ty));
//                     // } else {
//                     //     return Err(TypeError::InvalidTypeName(
//                     //         SourceLocation {
//                     //             line: decl.ret_ty.line,
//                     //             col: decl.ret_ty.col,
//                     //         },
//                     //         format!(
//                     //             "Return type '{}' for function '{}' does not exist.",
//                     //             decl.ret_ty.name, decl.name.name
//                     //         ),
//                     //     ));
//                     // }
//                 }
//                 _ => {}
//             }
//         }

//         Ok(())
//     }

//     // fn get_type_info(&self, symbol: &Symbol) -> Option<TypeInfo> {
//     //     // TODO: Parse primitives as keywords instead of structs
//     // }

//     fn pretty_ty(&self, ty: TypeInfo) -> String {
//         use crate::analysis::TypeInfo::*;

//         let string = match ty {
//             Number => "number".to_string(),
//             String => "string".to_string(),
//             Bool => "bool".to_string(),
//             Null => "burnt".to_string(),
//             Void => "void".to_string(),
//             Struct(id) => self.to_type_name(id),
//             Function(ret_ty, args) => {
//                 let args = args
//                     .iter()
//                     .map(|arg| self.to_type_name(*arg))
//                     .collect::<Vec<std::string::String>>()
//                     .join(", ");
//                 format!("pancake ({}): {}", args, self.to_type_name(ret_ty))
//             }
//             Array(ty) => {
//                 let ty = self.pretty_ty(*ty);
//                 format!("Array<{}>", ty)
//             }
//         };

//         string
//     }

//     fn to_type_name(&self, id: TypeId) -> String {
//         self.struct_decls[id].name.name.clone()
//     }
// }

// #[cfg(test)]
// mod tests {
//     use super::*;
//     use crate::{lexer, parser};

//     #[test]
//     fn test() {
//         match lexer::lex_tokens(
//             r#"
//             ain't 5#
//             "#
//             .to_string(),
//         ) {
//             Ok(tokens) => {
//                 let mut parser = parser::Parser::new(tokens);
//                 match parser.parse() {
//                     Ok(stmts) => {
//                         let mut tyck = TypeBuilder::new();
//                         match tyck.build(stmts) {
//                             Ok(typed_ast) => println!("{:#?}", typed_ast),
//                             Err(e) => println!("{:?}", e),
//                         }
//                         panic!()
//                     }
//                     Err(e) => {
//                         panic!("Parser error: {:?}", e);
//                     }
//                 }
//             }
//             Err(err) => {
//                 panic!("Lexer error: {}", err.message)
//             }
//         }
//     }
// }
