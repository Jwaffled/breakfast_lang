#[derive(Debug, Clone)]
pub enum Expr {
    Literal(Literal),
    Unary(UnaryOp, Box<Expr>),
    Binary(Box<Expr>, BinaryOp, Box<Expr>),
    Grouping(Box<Expr>),
    Logical(Box<Expr>, LogicalOp, Box<Expr>),
    Call(Box<Expr>, SourceLocation, Vec<Expr>),
    Get(Box<Expr>, Symbol),
    Variable(Symbol),
    Assign(Symbol, Box<Expr>),
    Set(Box<Expr>, Symbol, Box<Expr>),
    List(Vec<Expr>),
    Subscript {
        value: Box<Expr>,
        slice: Box<Expr>,
        source_location: SourceLocation,
    },
}

#[derive(Debug, Clone)]
pub enum Stmt<T> {
    Expr(T),
    Print(T),
    If(T, Box<Stmt<T>>, Option<Box<Stmt<T>>>),
    FunDecl(FunDecl),
    Return(SourceLocation, Option<T>),
    VarDecl(Symbol, Option<TypeAnnotation>, Option<T>),
    Block(Vec<Stmt<T>>),
    While(T, Box<Stmt<T>>, /* invert condition? */ bool),
    StructDecl(StructDecl),
}

#[derive(Debug, Clone)]
pub enum TypeAnnotation {
    Number,
    String,
    Bool,
    Void,
    Struct(Symbol),
    Function(Option<Symbol>, Vec<TypeAnnotation>, Box<TypeAnnotation>),
    Array(Box<TypeAnnotation>),
}

#[derive(Debug, Clone)]
pub struct StructDecl {
    pub name: Symbol,
    pub fields: Vec<Stmt<Expr>>,
}

impl StructDecl {
    pub(crate) fn create_native(name: String) -> Self {
        Self {
            name: Symbol {
                name,
                line: 0,
                col: 0,
            },
            fields: Vec::new(),
        }
    }
}

#[derive(Debug, Clone)]
pub enum Literal {
    Number(f64),
    String(String),
    True,
    False,
    Null,
}

#[derive(Debug, Clone)]
pub struct SourceLocation {
    pub line: usize,
    pub col: i64,
}

#[derive(Debug, Clone)]
pub struct Symbol {
    pub name: String,
    pub line: usize,
    pub col: i64,
}

#[derive(Debug, Clone)]
pub struct FunDecl {
    pub name: Symbol,
    pub params: Vec<(
        /* arg token */ Symbol,
        /* arg type */ TypeAnnotation,
    )>,
    pub body: Vec<Stmt<Expr>>,
    pub ret_ty: TypeAnnotation,
}

#[derive(Debug, Clone, Copy)]
pub enum UnaryOpType {
    Minus,
    Not,
}

#[derive(Debug, Clone, Copy)]
pub struct UnaryOp {
    pub op_type: UnaryOpType,
    pub line: usize,
    pub col: i64,
}

impl std::fmt::Display for UnaryOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use crate::ast::UnaryOpType::*;
        let string = match self.op_type {
            Not => "ain't",
            Minus => "-",
        };

        write!(f, "{}", string)
    }
}

#[derive(Debug, Clone, Copy)]
pub enum BinaryOpType {
    Plus,
    Minus,
    Star,
    Slash,
    EqualEqualTaste,
    LessThanTasteless,
    GreaterThanTastier,
}

impl std::fmt::Display for BinaryOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use crate::ast::BinaryOpType::*;
        let string = match self.op_type {
            Plus => "+",
            Minus => "-",
            Star => "*",
            Slash => "/",
            EqualEqualTaste => "taste",
            LessThanTasteless => "tasteless",
            GreaterThanTastier => "tastier",
        };

        write!(f, "{}", string)
    }
}

#[derive(Debug, Clone, Copy)]
pub struct BinaryOp {
    pub op_type: BinaryOpType,
    pub line: usize,
    pub col: i64,
}

#[derive(Debug, Clone, Copy)]
pub enum LogicalOpType {
    OrChop,
    AndBlend,
}

#[derive(Debug, Clone, Copy)]
pub struct LogicalOp {
    pub op_type: LogicalOpType,
    pub line: usize,
    pub col: i64,
}

impl std::fmt::Display for LogicalOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.op_type {
            LogicalOpType::OrChop => write!(f, "chop"),
            LogicalOpType::AndBlend => write!(f, "blend"),
        }
    }
}
