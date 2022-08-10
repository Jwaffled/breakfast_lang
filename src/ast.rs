#[derive(Debug, Clone)]
pub enum Expr {
    Literal(Literal),
    Unary(UnaryOp, Box<Expr>),
    Binary(Box<Expr>, BinaryOp, Box<Expr>),
    Grouping(Box<Expr>),
    Logical(Box<Expr>, LogicalOpType, Box<Expr>),
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
pub enum Stmt {
    Expr(Expr),
    Print(Expr),
    If(Expr, Box<Stmt>, Option<Box<Stmt>>),
    FunDecl(FunDecl),
    Return(SourceLocation, Option<Expr>),
    VarDecl(Symbol, Option<Symbol>, Option<Expr>),
    Block(Vec<Stmt>),
    While(Expr, Box<Stmt>, /* invert condition? */ bool),
    StructDecl(StructDecl),
}

#[derive(Debug, Clone)]
pub struct StructDecl {
    pub name: Symbol,
    pub fields: Vec<Stmt>,
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
    pub params: Vec<Symbol>,
    pub body: Vec<Stmt>,
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
