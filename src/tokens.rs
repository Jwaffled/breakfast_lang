#[derive(Clone, Debug, PartialEq, Copy)]
pub enum TokenType {
    // Standard token types. Nothing really weird here
    LeftParen,
    RightParen,
    OpenScopeBar,
    CloseScopeBar,
    LeftBracket,
    RightBracket,
    Dot,
    Semicolon,
    Colon,
    Comma,

    Plus,
    Minus,
    Star,
    Slash,
    Not,

    // Weirder operator tokens
    AssignFork,
    OrChop,
    AndBlend,
    EqualEqualTaste,
    LessThanTasteless,
    GreaterThanTastier,

    // Literals
    Number,
    Identifier,
    String,

    // One-word keywords
    TrueCrispy,
    FalseRaw,
    NullBurnt,
    VarFood,
    WhileFlipwhen,
    ForPrepare,
    If,
    Else,
    DoWhileMix,
    DoWhileUntil,
    ReturnPlate,
    StructOmelette,
    FunctionPancake,
    ForPreheat,
    ForAt,
    PrintServe,

    ForCookUntil,
    ForStir,

    // End of file
    Eof,
}

#[derive(Clone, Debug)]
pub enum Literal {
    Number(f64),
    String(String),
    Identifier(String),
}

#[derive(Clone, Debug)]
pub struct Token {
    pub token_type: TokenType,
    pub lexeme: String,
    pub literal: Option<Literal>,
    pub line: usize,
    pub col: i64,
}

impl Token {
    pub fn new(
        token_type: TokenType,
        lexeme: String,
        literal: Option<Literal>,
        line: usize,
        col: i64,
    ) -> Self {
        Token {
            token_type,
            lexeme,
            literal,
            line,
            col,
        }
    }
}
