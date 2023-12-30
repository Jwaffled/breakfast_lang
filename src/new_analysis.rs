use std::collections::HashMap;

use crate::ast::{
    BinaryOp, BinaryOpType, Expr, Literal, LogicalOp, SourceLocation, Stmt, StructDecl, UnaryOp,
    UnaryOpType,
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
}

#[derive(Clone)]
struct SymbolEnvironment {
    enclosing: Option<Box<SymbolEnvironment>>,
    locals: HashMap<String, TypeInfo>,
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
}

struct TypeEnvironment {
    symbols: SymbolEnvironment,
    structs: HashMap<String, StructDecl<TypedExpr>>,
}

impl TypeEnvironment {
    pub fn new() -> Self {
        Self {
            symbols: SymbolEnvironment::new(),
            structs: HashMap::new(),
        }
    }
    fn resolve_type_name(&self, ty: TypeInfo) -> String {
        match ty {
            TypeInfo::Number => String::from("Number"),
            TypeInfo::String => String::from("String"),
            TypeInfo::Bool => String::from("Bool"),
            TypeInfo::Null => String::from("Null"),
            TypeInfo::Void => String::from("Void"),
            TypeInfo::Struct(id) => format!("Struct({})", id),
            TypeInfo::Function(ret, args) => format!("Function({:?}): {:?}", args, ret),
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

pub fn typecheck_ast(ast: Vec<Stmt<Expr>>) -> Result<TypedAST, TypeError> {
    let mut env = TypeEnvironment::new();

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
