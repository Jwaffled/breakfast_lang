use std::collections::HashMap;

use crate::ast::{
    BinaryOp, BinaryOpType, Expr, FunDecl, Literal, LogicalOp, SourceLocation, Stmt, StructDecl,
    Symbol, TypeAnnotation, UnaryOp, UnaryOpType,
};

#[derive(Debug, Eq, PartialEq, Clone)]
pub enum TypeInfo {
    Number,
    String,
    Bool,
    Null,
    Void,
    Struct(String),
    Function(Box<TypeInfo>, Vec<TypeInfo>), // Return type, argument types
    Array(Box<TypeInfo>),
}

impl TypeInfo {
    fn from_annotation(
        annotation: &TypeAnnotation,
        env: &TypeEnvironment,
    ) -> Result<Self, TypeError> {
        match annotation {
            TypeAnnotation::Number => Ok(TypeInfo::Number),
            TypeAnnotation::String => Ok(TypeInfo::String),
            TypeAnnotation::Bool => Ok(TypeInfo::Bool),
            TypeAnnotation::Void => Ok(TypeInfo::Void),
            TypeAnnotation::Struct(symbol) => {
                if env.structs.contains_key(&symbol.name) {
                    Ok(TypeInfo::Struct(symbol.name.clone()))
                } else {
                    Err(TypeError::StructNotDefined(
                        SourceLocation::new(symbol.line, symbol.col),
                        format!("Struct '{}' does not exist", symbol.name),
                    ))
                }
            }
            TypeAnnotation::Function(_, args, ret_ty) => {
                // We do not care if it is a named function or not, just ignore the name
                let mut converted = vec![];
                for arg in args {
                    converted.push(Self::from_annotation(arg, env)?);
                }
                Ok(TypeInfo::Function(
                    Box::new(Self::from_annotation(ret_ty, env)?),
                    converted,
                ))
            }
            TypeAnnotation::Array(inner) => Ok(TypeInfo::Array(Box::new(
                TypeInfo::from_annotation(inner, env)?,
            ))),
        }
    }
}

#[derive(Debug)]
pub struct Typed<T: Clone> {
    value: T,
    ty: TypeInfo,
}

impl<T: Clone> Typed<T> {
    pub fn new(ty: TypeInfo, value: T) -> Self {
        Self { ty, value }
    }
}

pub type TypedExpr = Typed<Expr>;
pub type TypedAST = Vec<Stmt<TypedExpr>>;
pub type ExprResult = Result<TypedExpr, TypeError>;

#[derive(Debug)]
pub enum TypeError {
    InvalidOperator(SourceLocation, String),
    ExpectedType(SourceLocation, String),
    DuplicateFuncDecl(SourceLocation, String),
    DuplicateStructDecl(SourceLocation, String),
    DuplicateVarDecl(SourceLocation, String),
    VariableNotDefined(SourceLocation, String),
    StructNotDefined(SourceLocation, String),
}

#[derive(Clone)]
struct SymbolEnvironment {
    enclosing: Option<Box<SymbolEnvironment>>,
    locals: HashMap<String, (Option<TypeInfo>, SourceLocation)>,
}

enum LookupResult {
    Ok(TypeInfo),
    NoTypeInfo(SourceLocation),
    Undeclared,
}

impl SymbolEnvironment {
    fn new() -> Self {
        Self {
            enclosing: None,
            locals: HashMap::new(),
        }
    }

    fn with_enclosing(enclosing: SymbolEnvironment) -> Self {
        SymbolEnvironment {
            enclosing: Some(Box::new(enclosing)),
            locals: HashMap::new(),
        }
    }

    fn define(&mut self, symbol: &Symbol) {
        self.locals.insert(
            symbol.name.clone(),
            (None, SourceLocation::new(symbol.line, symbol.col)),
        );
    }

    fn define_and_assign(&mut self, symbol: &Symbol, ty: TypeInfo) {
        self.locals.insert(
            symbol.name.clone(),
            (Some(ty), SourceLocation::new(symbol.line, symbol.col)),
        );
    }

    fn assign(&mut self, name: &String, ty: TypeInfo) {
        if let Some((maybe_ty, _)) = self.locals.get_mut(name) {
            *maybe_ty = Some(ty);
        } else {
            if let Some(enclosing) = &mut self.enclosing {
                enclosing.assign(name, ty);
            }
        }
    }

    fn lookup_local(&self, name: &String) -> LookupResult {
        match self.locals.get(name) {
            Some((maybe_ty, loc)) => {
                if let Some(ty) = maybe_ty {
                    LookupResult::Ok(ty.clone())
                } else {
                    LookupResult::NoTypeInfo(loc.clone())
                }
            }
            None => LookupResult::Undeclared,
        }
    }

    fn lookup_all(&self, name: &Symbol) -> LookupResult {
        let local_res = self.lookup_local(&name.name);
        match local_res {
            LookupResult::Undeclared => match &self.enclosing {
                Some(enc) => enc.lookup_all(name),
                None => local_res,
            },
            _ => local_res,
        }
    }

    fn has_type_info(&self, name: &Symbol) -> bool {
        match self.lookup_all(name) {
            LookupResult::Ok(_) => true,
            _ => false,
        }
    }
}

struct TypeEnvironment {
    symbols: SymbolEnvironment,
    structs: HashMap<String, StructDecl<Expr>>,
    functions: HashMap<String, FunDecl<Expr>>,
}

impl TypeEnvironment {
    pub fn new(ast: &Vec<Stmt<Expr>>) -> Result<Self, TypeError> {
        let mut env = Self {
            symbols: SymbolEnvironment::new(),
            structs: HashMap::new(),
            functions: HashMap::new(),
        };

        env.register(ast)?;
        Ok(env)
    }

    fn define_sym(&mut self, symbol: &Symbol) -> Result<(), TypeError> {
        if self.symbols.has_type_info(symbol) {
            Err(TypeError::DuplicateVarDecl(
                SourceLocation::new(symbol.line, symbol.col),
                format!("Variable '{}' defined more than once", symbol.name),
            ))
        } else {
            self.symbols.define(symbol);
            Ok(())
        }
    }

    fn assign_sym(&mut self, symbol: &Symbol, ty: TypeInfo) -> Result<(), TypeError> {
        match self.symbols.lookup_all(symbol) {
            LookupResult::Ok(_) => {
                unreachable!("If you got here you seriously fucked something up")
            }
            LookupResult::NoTypeInfo(_) => self.symbols.assign(&symbol.name, ty),
            LookupResult::Undeclared => {
                return Err(TypeError::VariableNotDefined(
                    SourceLocation::new(symbol.line, symbol.col),
                    format!("Variable '{}' assigned to before definition", symbol.name),
                ));
            }
        }

        Ok(())
    }

    fn define_and_assign_sym(&mut self, symbol: &Symbol, ty: TypeInfo) -> Result<(), TypeError> {
        if self.symbols.has_type_info(symbol) {
            Err(TypeError::DuplicateVarDecl(
                SourceLocation::new(symbol.line, symbol.col),
                format!("Variable '{}' defined more than once", symbol.name),
            ))
        } else {
            self.symbols.define_and_assign(symbol, ty);
            Ok(())
        }
    }

    fn clean_env(&self) -> Self {
        Self {
            symbols: SymbolEnvironment::new(),
            structs: self.structs.clone(),
            functions: self.functions.clone(),
        }
    }

    fn register(&mut self, ast: &Vec<Stmt<Expr>>) -> Result<(), TypeError> {
        // Register function and struct types
        for node in ast {
            match node {
                Stmt::FunDecl(decl) => {
                    if self.functions.contains_key(&decl.name.name) {
                        return Err(TypeError::DuplicateFuncDecl(
                            SourceLocation::new(decl.name.line, decl.name.col),
                            format!("Function '{}' already defined", decl.name.name),
                        ));
                    }

                    self.functions.insert(decl.name.name.clone(), decl.clone());
                }

                Stmt::StructDecl(decl) => {
                    if self.structs.contains_key(&decl.name.name) {
                        return Err(TypeError::DuplicateStructDecl(
                            SourceLocation::new(decl.name.line, decl.name.col),
                            format!("Struct '{}' already defined", decl.name.name),
                        ));
                    }

                    self.structs.insert(decl.name.name.clone(), decl.clone());
                }
                _ => {}
            }
        }

        // Register variables
        for node in ast {
            match node {
                Stmt::VarDecl(symbol, maybe_ty, maybe_init) => {
                    if !maybe_ty.is_some() && !maybe_init.is_some() {
                        self.symbols.define(symbol);
                    } else if maybe_ty.is_some() && maybe_init.is_some() {
                        // Check if type annotation and init expr types agree
                        let ty = TypeInfo::from_annotation(&maybe_ty.clone().unwrap(), self)?;
                        let expr_ty = maybe_init.clone().unwrap().check(self)?;
                        if ty != expr_ty.ty {
                            return Err(TypeError::ExpectedType(
                                SourceLocation::new(symbol.line, symbol.col),
                                "Expected initialization to agree with type annotation".to_string(),
                            ));
                        }
                        self.symbols.define_and_assign(symbol, ty)
                    } else {
                        let ty = {
                            if maybe_ty.is_some() {
                                TypeInfo::from_annotation(&maybe_ty.clone().unwrap(), self)?
                            } else {
                                maybe_init.clone().unwrap().check(self)?.ty
                            }
                        };
                        self.symbols.define_and_assign(symbol, ty);
                    }
                }
                _ => {}
            }
        }

        Ok(())
    }

    fn resolve_type_name(&self, ty: TypeInfo) -> String {
        match ty {
            TypeInfo::Number => String::from("Number"),
            TypeInfo::String => String::from("String"),
            TypeInfo::Bool => String::from("Bool"),
            TypeInfo::Null => String::from("Null"),
            TypeInfo::Void => String::from("Void"),
            TypeInfo::Struct(id) => format!("Struct({})", id),
            TypeInfo::Function(ret, args) => format!(
                "Function({}): {}",
                args.iter()
                    .map(|x| self.resolve_type_name(x.clone()))
                    .collect::<Vec<String>>()
                    .join(","),
                self.resolve_type_name(*ret)
            ),
            TypeInfo::Array(inner) => format!("Array<{}>", self.resolve_type_name(*inner)),
        }
    }
}

trait TypeCheck {
    type Checked;

    fn check(&self, env: &mut TypeEnvironment) -> Result<Self::Checked, TypeError>;
}

impl TypeCheck for Stmt<Expr> {
    type Checked = Stmt<TypedExpr>;

    fn check(&self, env: &mut TypeEnvironment) -> Result<Self::Checked, TypeError> {
        match self {
            Stmt::Expr(expr) => {
                let expr = expr.check(env)?;
                Ok(Stmt::Expr(expr))
            }

            Stmt::Block(stmts) => {
                env.symbols = SymbolEnvironment::with_enclosing(env.symbols.clone());
                let mut checked_stmts = vec![];
                for stmt in stmts {
                    checked_stmts.push(stmt.check(env)?);
                }

                if let Some(enclosing) = env.symbols.enclosing.clone() {
                    env.symbols = *enclosing;
                }

                Ok(Stmt::Block(checked_stmts))
            }

            Stmt::Print(expr) => {
                let expr = expr.check(env)?;
                Ok(Stmt::Print(expr))
            }

            Stmt::If(expr, body, maybe_else, loc) => {
                let expr = expr.check(env)?;
                if expr.ty != TypeInfo::Bool {
                    Err(TypeError::ExpectedType(
                        loc.clone(),
                        format!("If condition does not evaluate to a boolean"),
                    ))
                } else {
                    let body = body.check(env)?;
                    let else_body = if maybe_else.is_some() {
                        let checked = maybe_else.clone().unwrap().check(env)?;
                        Some(Box::new(checked))
                    } else {
                        None
                    };

                    Ok(Stmt::If(expr, Box::new(body), else_body, loc.clone()))
                }
            }

            Stmt::StructDecl(decl) => {
                let mut fields = vec![];
                for field in &decl.fields {
                    fields.push(field.check(env)?);
                }

                Ok(Stmt::StructDecl(StructDecl {
                    name: decl.name.clone(),
                    fields,
                }))
            }

            Stmt::FunDecl(decl) => {
                // sanitize type environment
                // add args to type environment
                // typecheck body
                // ggs go next
                let mut sanitized_env = env.clean_env();
                for (sym, arg_ty) in &decl.params {
                    sanitized_env.define_and_assign_sym(
                        sym,
                        TypeInfo::from_annotation(arg_ty, &sanitized_env)?,
                    )?;
                }
                let mut body = vec![];
                for stmt in &decl.body {
                    body.push(stmt.check(&mut sanitized_env)?);
                }

                Ok(Stmt::FunDecl(FunDecl {
                    name: decl.name.clone(),
                    params: decl.params.clone(),
                    body,
                    ret_ty: decl.ret_ty.clone(),
                }))
            }

            Stmt::VarDecl(symbol, maybe_ty, maybe_init) => {
                let checked = if let Some(init) = maybe_init {
                    Some(init.check(env)?)
                } else {
                    None
                };

                Ok(Stmt::VarDecl(symbol.clone(), maybe_ty.clone(), checked))
            }

            other => {
                panic!("Stmt {:?} not implemented yet", other);
            }
        }
    }
}

impl TypeCheck for Expr {
    type Checked = Typed<Expr>;

    fn check(&self, env: &mut TypeEnvironment) -> Result<Self::Checked, TypeError> {
        match self {
            Self::Literal(literal) => literal.check(env),
            Self::Binary(lhs, op, rhs) => check_binary(lhs, *op, rhs, env),
            Self::Unary(op, expr) => check_unary(*op, expr, env),
            Self::Logical(lhs, op, rhs) => check_logical(lhs, *op, rhs, env),
            // For assignment, just return void as the type, I made a fundamental mistake making assignment an Expr instead of a Stmt

            other => {
                panic!("Expr {:?} not implemented yet", other);
            }
        }
    }
}

impl TypeCheck for Literal {
    type Checked = Typed<Expr>;

    fn check(&self, env: &mut TypeEnvironment) -> Result<Self::Checked, TypeError> {
        let ty = match self {
            Literal::False | Literal::True => TypeInfo::Bool,
            Literal::Null => TypeInfo::Null,
            Literal::Number(_) => TypeInfo::Number,
            Literal::String(_) => TypeInfo::String,
        };

        Ok(Typed::new(ty, Expr::Literal(self.clone())))
    }
}

pub fn typecheck_ast(ast: &Vec<Stmt<Expr>>) -> Result<TypedAST, TypeError> {
    let mut env = TypeEnvironment::new(ast)?;

    ast.into_iter()
        .map(|node| node.check(&mut env))
        .collect::<Result<TypedAST, TypeError>>()
}

fn check_binary(
    lhs: &Box<Expr>,
    op: BinaryOp,
    rhs: &Box<Expr>,
    env: &mut TypeEnvironment,
) -> ExprResult {
    let typed_lhs = lhs.check(env)?;
    let typed_rhs = rhs.check(env)?;
    let ty = match (typed_lhs.ty, typed_rhs.ty) {
        (TypeInfo::Number, TypeInfo::Number) => match op.op_type {
            BinaryOpType::Plus | BinaryOpType::Minus | BinaryOpType::Slash | BinaryOpType::Star => {
                Ok(TypeInfo::Number)
            }
            BinaryOpType::EqualEqualTaste
            | BinaryOpType::GreaterThanTastier
            | BinaryOpType::LessThanTasteless => Ok(TypeInfo::Bool),
        },
        (TypeInfo::String, TypeInfo::String) => match op.op_type {
            BinaryOpType::Plus => Ok(TypeInfo::String),
            _ => Err(TypeError::InvalidOperator(
                SourceLocation::new(op.line, op.col),
                format!("Cannot use operator '{}' on types String and String", op),
            )),
        },
        (TypeInfo::Bool, TypeInfo::Bool) => match op.op_type {
            BinaryOpType::EqualEqualTaste => Ok(TypeInfo::Bool),
            _ => Err(TypeError::InvalidOperator(
                SourceLocation::new(op.line, op.col),
                format!("Cannot use operator '{}' on types Bool and Bool", op),
            )),
        },
        (l_ty, r_ty) => Err(TypeError::InvalidOperator(
            SourceLocation::new(op.line, op.col),
            format!(
                "Cannot use operator '{}' on types {} and {}",
                op,
                env.resolve_type_name(l_ty),
                env.resolve_type_name(r_ty)
            ),
        )),
    };

    if let Ok(ty) = ty {
        Ok(Typed::new(ty, Expr::Binary(lhs.clone(), op, rhs.clone())))
    } else {
        Err(ty.unwrap_err())
    }
}

fn check_unary(op: UnaryOp, expr: &Box<Expr>, env: &mut TypeEnvironment) -> ExprResult {
    let ty_e = expr.check(env)?;
    let ty = match (op.op_type, ty_e.ty) {
        (UnaryOpType::Minus, TypeInfo::Number) => Ok(TypeInfo::Number),
        (UnaryOpType::Not, TypeInfo::Bool) => Ok(TypeInfo::Bool),
        (_, ty) => Err(TypeError::InvalidOperator(
            SourceLocation::new(op.line, op.col),
            format!(
                "Cannot use operator '{}' on type '{}'",
                op,
                env.resolve_type_name(ty)
            ),
        )),
    };

    if let Ok(ty) = ty {
        Ok(Typed::new(ty, Expr::Unary(op, expr.clone())))
    } else {
        Err(ty.unwrap_err())
    }
}

fn check_logical(
    lhs: &Box<Expr>,
    op: LogicalOp,
    rhs: &Box<Expr>,
    env: &mut TypeEnvironment,
) -> ExprResult {
    let typed_lhs = lhs.check(env)?;
    let typed_rhs = rhs.check(env)?;

    let ty = match (typed_lhs.ty, typed_rhs.ty) {
        (TypeInfo::Bool, TypeInfo::Bool) => Ok(TypeInfo::Bool),
        (l_ty, r_ty) => Err(TypeError::InvalidOperator(
            SourceLocation::new(op.line, op.col),
            format!(
                "Cannot use operator '{}' on types {} and {}",
                op,
                env.resolve_type_name(l_ty),
                env.resolve_type_name(r_ty)
            ),
        )),
    };

    if let Ok(ty) = ty {
        Ok(Typed::new(ty, Expr::Logical(lhs.clone(), op, rhs.clone())))
    } else {
        Err(ty.unwrap_err())
    }
}
