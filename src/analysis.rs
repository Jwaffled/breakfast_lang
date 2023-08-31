use std::{collections::HashMap, fmt::Display};

use crate::ast::{
    BinaryOp, BinaryOpType, Expr, Literal, LogicalOp, SourceLocation, Stmt, Symbol, TypeAnnotation,
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
    Array(Box<TypeInfo>),
}

impl Display for TypeInfo {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Number => write!(f, "Number"),
            Self::String => write!(f, "String"),
            Self::Bool => write!(f, "Bool"),
            Self::Null => write!(f, "Null"),
            Self::Void => write!(f, "Void"),
            Self::Struct(_) => write!(f, "Object"),
            Self::Function(_, _) => write!(f, "Function"),
            Self::Array(_) => write!(f, "Array"),
        }
    }
}

enum TypeError {
    StructAlreadyDefined(SourceLocation),
    FunctionAlreadyDefined(SourceLocation),
    InvalidBinaryOp(SourceLocation, String),
    InvalidUnaryOp(SourceLocation, String),
    InvalidTypeName(SourceLocation, String),
    NoTypeInfo(SourceLocation, String),
    MismatchedTypes(SourceLocation, String),
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
            Self::MismatchedTypes(loc, message) => write!(
                f,
                "TypeError: Mismatched types on line {} col {}: {}",
                loc.line, loc.col, message
            ),
        }
    }
}

#[derive(Debug)]
struct SymbolTableEntry<T> {
    id: usize,
    data: T,
}

impl<T> SymbolTableEntry<T> {
    fn new(id: usize, data: T) -> Self {
        Self { id, data }
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

#[derive(Debug)]
struct SymbolTable<T> {
    symbols: HashMap<String, SymbolTableEntry<T>>,
    // Perhaps add a way back?
    next_id: usize,
}

impl<T> SymbolTable<T> {
    fn new() -> Self {
        Self {
            symbols: HashMap::new(),
            next_id: 0,
        }
    }

    fn get_or_intern(&mut self, symbol: &str, data: T) -> &SymbolTableEntry<T> {
        if self.symbols.contains_key(symbol) {
            self.symbols.get(symbol).unwrap()
        } else {
            let new_entry = SymbolTableEntry::new(self.next_id, data);
            self.symbols.insert(symbol.to_string(), new_entry);
            self.next_id += 1;
            self.symbols.get(symbol).unwrap()
        }
        // if let Some(entry) = self.symbols.get(symbol) {
        //     entry
        // } else {
        //     let entry = SymbolTableEntry::new(self.next_id, data);
        //     self.symbols.insert(symbol.to_string(), entry);
        //     self.next_id += 1;
        //     self.symbols.get(symbol).unwrap()
        // }
    }

    fn intern(&mut self, symbol: &str, data: T) -> &SymbolTableEntry<T> {
        if self.symbols.contains_key(symbol) {
            let entry = self.symbols.get_mut(symbol).unwrap();
            entry.data = data;
            entry
        } else {
            let entry = SymbolTableEntry::new(self.next_id, data);
            self.symbols.insert(symbol.to_string(), entry);
            self.next_id += 1;
            self.symbols.get(symbol).unwrap()
        }
    }

    fn get(&self, symbol: &str) -> Option<&SymbolTableEntry<T>> {
        self.symbols.get(symbol)
    }

    fn has(&self, symbol: &str) -> bool {
        self.symbols.contains_key(symbol)
    }
}

type TypedAST = Vec<Typed<Stmt>>;

#[derive(Debug)]
struct TypeBuilder {
    struct_tys: SymbolTable<Option<Vec<TypeInfo>>>,
    fn_tys: HashMap<String, Option<(Vec<TypeInfo>, TypeInfo)>>, // (Arg types, return type)
    // struct_table: SymbolTable<Vec<TypeInfo>>,
    // fn_table: SymbolTable<(Vec<TypeInfo>, TypeInfo)>,
    symbol_table: SymbolTable<usize>, // idk what to do with this yet
}

impl TypeBuilder {
    pub fn new() -> Self {
        Self {
            struct_tys: SymbolTable::new(),
            fn_tys: HashMap::new(),
            // struct_table: SymbolTable::new(),
            // fn_table: SymbolTable::new(),
            symbol_table: SymbolTable::new(),
        }
    }

    pub fn build(&mut self, ast: Vec<Stmt>) -> Result<TypedAST, TypeError> {
        self.resolve_all(&ast)?;
        print!("{:#?}", self);
        ast.into_iter()
            .map(|node| self.build_stmt(node))
            .collect::<Result<TypedAST, TypeError>>()
    }

    fn build_stmt(&mut self, stmt: Stmt) -> Result<Typed<Stmt>, TypeError> {
        match stmt {
            Stmt::Expr(expr) => {
                let expr = self.build_expr(expr)?;
                Ok(Typed::new(expr.ty, Stmt::Expr(expr.value)))
            }

            Stmt::VarDecl(symbol, maybe_ty, maybe_init) => {
                self.build_var_decl(symbol, maybe_ty, maybe_init)
            }

            other => {
                panic!("Stmt {:?} not implemented yet!", other);
            }
        }
    }

    fn build_var_decl(
        &mut self,
        symbol: Symbol,
        maybe_ty: Option<TypeAnnotation>,
        maybe_init: Option<Expr>,
    ) -> Result<Typed<Stmt>, TypeError> {
        if maybe_ty.is_none() && maybe_init.is_none() {
            Err(TypeError::NoTypeInfo(
                SourceLocation {
                    line: symbol.line,
                    col: symbol.col,
                },
                "Either an initial value or a type must be supplied when declaring fields"
                    .to_string(),
            ))
        } else {
            if let Some(ty) = maybe_ty {
                // Check if types agree
                let annotation = self.resolve_type(&ty)?;
                if let Some(init) = maybe_init {
                    let init_ty = self.build_expr(init)?;
                    if init_ty.ty == annotation {
                        Ok(Typed::new(
                            init_ty.ty,
                            Stmt::VarDecl(symbol, Some(ty), Some(init_ty.value)),
                        ))
                    } else {
                        Err(TypeError::MismatchedTypes(
                            SourceLocation {
                                line: symbol.line,
                                col: symbol.col,
                            },
                            "Conflicting type annotation and initialization expression".to_string(),
                        ))
                    }
                } else {
                    Ok(Typed::new(
                        annotation,
                        Stmt::VarDecl(symbol, Some(ty), maybe_init),
                    ))
                }
            } else {
                let init = self.build_expr(maybe_init.unwrap())?;
                Ok(Typed::new(
                    init.ty,
                    Stmt::VarDecl(symbol, maybe_ty, Some(init.value)),
                ))
            }
        }
    }

    fn build_expr(&mut self, expr: Expr) -> Result<Typed<Expr>, TypeError> {
        match expr {
            Expr::Literal(literal) => self.build_literal(literal),

            Expr::Binary(lhs, op, rhs) => self.build_binary(lhs, op, rhs),

            Expr::Unary(op, expr) => self.build_unary(op, expr),

            Expr::Logical(lhs, op, rhs) => self.build_logical(lhs, op, rhs),

            other => {
                panic!("Expression {:?} not implemented yet!", other)
            }
        }
    }

    fn build_logical(
        &mut self,
        lhs: Box<Expr>,
        op: LogicalOp,
        rhs: Box<Expr>,
    ) -> Result<Typed<Expr>, TypeError> {
        let typed_lhs = self.build_expr(*lhs)?;
        let typed_rhs = self.build_expr(*rhs)?;
        match (typed_lhs.ty, typed_rhs.ty) {
            (TypeInfo::Bool, TypeInfo::Bool) => Ok(Typed::new(
                TypeInfo::Bool,
                Expr::Logical(Box::new(typed_lhs.value), op, Box::new(typed_rhs.value)),
            )),
            (lhs_ty, rhs_ty) => Err(TypeError::InvalidBinaryOp(
                SourceLocation { line: 0, col: 0 },
                format!(
                    "Cannot use logical operator '{}' on types {} and {}",
                    op, lhs_ty, rhs_ty
                ),
            )),
        }
    }

    fn build_binary(
        &mut self,
        lhs: Box<Expr>,
        op: BinaryOp,
        rhs: Box<Expr>,
    ) -> Result<Typed<Expr>, TypeError> {
        let typed_lhs = self.build_expr(*lhs)?;
        let typed_rhs = self.build_expr(*rhs)?;
        match (typed_lhs.ty, typed_rhs.ty) {
            (TypeInfo::Number, TypeInfo::Number) => match op.op_type {
                BinaryOpType::Minus
                | BinaryOpType::Plus
                | BinaryOpType::Slash
                | BinaryOpType::Star => Ok(Typed::new(
                    TypeInfo::Number,
                    Expr::Binary(Box::new(typed_lhs.value), op, Box::new(typed_rhs.value)),
                )),
                BinaryOpType::EqualEqualTaste
                | BinaryOpType::GreaterThanTastier
                | BinaryOpType::LessThanTasteless => Ok(Typed::new(
                    TypeInfo::Bool,
                    Expr::Binary(Box::new(typed_lhs.value), op, Box::new(typed_rhs.value)),
                )),
            },
            (TypeInfo::String, TypeInfo::String) => match op.op_type {
                BinaryOpType::Plus => Ok(Typed::new(
                    TypeInfo::String,
                    Expr::Binary(Box::new(typed_lhs.value), op, Box::new(typed_rhs.value)),
                )),
                _ => Err(TypeError::InvalidBinaryOp(
                    SourceLocation {
                        line: op.line,
                        col: op.col,
                    },
                    format!(
                        "Cannot use binary operator '{}' on types String and String",
                        op
                    ),
                )),
            },
            (TypeInfo::Bool, TypeInfo::Bool) => match op.op_type {
                BinaryOpType::EqualEqualTaste => Ok(Typed::new(
                    TypeInfo::Bool,
                    Expr::Binary(Box::new(typed_lhs.value), op, Box::new(typed_rhs.value)),
                )),
                _ => Err(TypeError::InvalidBinaryOp(
                    SourceLocation {
                        line: op.line,
                        col: op.col,
                    },
                    format!("Cannot use binary operator '{}' on types Bool and Bool", op),
                )),
            },
            (lhs_ty, rhs_ty) => Err(TypeError::InvalidBinaryOp(
                SourceLocation {
                    line: op.line,
                    col: op.col,
                },
                format!(
                    "Cannot use binary operator '{}' on types {} and {}",
                    op, lhs_ty, rhs_ty
                ),
            )),
        }
    }

    fn build_unary(&mut self, op: UnaryOp, expr: Box<Expr>) -> Result<Typed<Expr>, TypeError> {
        let typed_expr = self.build_expr(*expr)?;
        match (op.op_type, typed_expr.ty) {
            (UnaryOpType::Minus, TypeInfo::Number) => Ok(Typed::new(
                TypeInfo::Number,
                Expr::Unary(op, Box::new(typed_expr.value)),
            )),
            (UnaryOpType::Not, TypeInfo::Bool) => Ok(Typed::new(
                TypeInfo::Bool,
                Expr::Unary(op, Box::new(typed_expr.value)),
            )),
            (_, type_info) => Err(TypeError::InvalidUnaryOp(
                SourceLocation {
                    line: op.line,
                    col: op.col,
                },
                format!(
                    "Unary operator '{}' cannot be used on type '{}'",
                    op, type_info
                ),
            )),
        }
    }

    fn build_literal(&mut self, literal: Literal) -> Result<Typed<Expr>, TypeError> {
        let lit = match literal {
            Literal::False | Literal::True => Typed::new(TypeInfo::Bool, literal),
            Literal::Null => Typed::new(TypeInfo::Null, literal),
            Literal::Number(_) => Typed::new(TypeInfo::Number, literal),
            Literal::String(_) => Typed::new(TypeInfo::String, literal),
        };
        Ok(Typed::new(lit.ty, Expr::Literal(lit.value)))
    }

    fn resolve_all(&mut self, ast: &[Stmt]) -> Result<(), TypeError> {
        self.resolve_struct_names(ast)?;
        for node in ast {
            match node {
                Stmt::StructDecl(struct_decl) => {
                    if self.struct_tys.has(&struct_decl.name.name) {
                        if self
                            .struct_tys
                            .get(&struct_decl.name.name)
                            .unwrap()
                            .data
                            .is_some()
                        {
                            return Err(TypeError::StructAlreadyDefined(SourceLocation {
                                line: struct_decl.name.line,
                                col: struct_decl.name.col,
                            }));
                        }

                        let mut field_tys = vec![];
                        for field in &struct_decl.fields {
                            let typed_field = self.build_stmt(field.clone())?;
                            field_tys.push(typed_field.ty);
                        }
                        self.struct_tys
                            .intern(&struct_decl.name.name, Some(field_tys));
                    } else {
                        //self.struct_tys.put(&struct_decl.name.name);
                        // Resolve inner types
                        let mut field_tys = vec![];
                        for field in &struct_decl.fields {
                            let typed_field = self.build_stmt(field.clone())?;
                            field_tys.push(typed_field.ty);
                        }
                        self.struct_tys
                            .intern(&struct_decl.name.name, Some(field_tys));
                    }
                }

                Stmt::FunDecl(fun_decl) => {
                    if self.fn_tys.contains_key(&fun_decl.name.name) {
                        return Err(TypeError::FunctionAlreadyDefined(SourceLocation {
                            line: fun_decl.name.line,
                            col: fun_decl.name.col,
                        }));
                    } else {
                        let mut arg_tys = vec![];
                        for (_, ty) in &fun_decl.params {
                            let resolved_ty = self.resolve_type(ty)?;
                            arg_tys.push(resolved_ty);
                        }

                        // Resolve arg & return types
                    }
                }

                _ => {}
            }
        }

        Ok(())
    }

    fn resolve_struct_names(&mut self, ast: &[Stmt]) -> Result<(), TypeError> {
        for node in ast {
            match node {
                Stmt::StructDecl(decl) => {
                    self.struct_tys.intern(&decl.name.name, None);
                }
                _ => {}
            }
        }

        Ok(())
    }

    fn resolve_type(&self, ty: &TypeAnnotation) -> Result<TypeInfo, TypeError> {
        match ty {
            TypeAnnotation::Bool => Ok(TypeInfo::Bool),
            TypeAnnotation::Number => Ok(TypeInfo::Number),
            TypeAnnotation::String => Ok(TypeInfo::String),
            TypeAnnotation::Void => Ok(TypeInfo::Void),
            TypeAnnotation::Struct(symbol) => {
                if let Some(entry) = self.struct_tys.get(&symbol.name) {
                    Ok(TypeInfo::Struct(entry.id))
                } else {
                    Err(TypeError::InvalidTypeName(
                        SourceLocation {
                            line: symbol.line,
                            col: symbol.col,
                        },
                        symbol.name.clone(),
                    ))
                }
            }
            _ => panic!("Not implemented yet"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{lexer, parser};

    #[test]
    fn test() {
        match lexer::lex_tokens(
            r#"
            omelette MyStruct |> thing: cal# thingTwo: MyStruct# <|
            "#
            .to_string(),
        ) {
            Ok(tokens) => {
                let mut parser = parser::Parser::new(tokens);
                match parser.parse() {
                    Ok(stmts) => {
                        let mut tyck = TypeBuilder::new();
                        match tyck.build(stmts) {
                            Ok(typed_ast) => println!("{:#?}", typed_ast),
                            Err(e) => println!("{:?}", e),
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
