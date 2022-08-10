#[derive(Debug, Clone)]
pub enum Type {
    String,
    Number,
    Instance,
    Function,
    Null,
    Bool,
}

#[derive(Debug, Clone)]
pub enum HLIRExpr {}

#[derive(Debug, Clone)]
pub enum HLIRStmt {}
