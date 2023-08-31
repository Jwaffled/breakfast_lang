use phf::phf_map;

use crate::tokens::{Literal, Token, TokenType};

static OW_KEYWORDS: phf::Map<&'static str, TokenType> = phf_map! {
    "crispy" => TokenType::TrueCrispy,
    "raw" => TokenType::FalseRaw,
    "burnt" => TokenType::NullBurnt,
    "food" => TokenType::VarFood,
    "flipwhen" => TokenType::WhileFlipwhen,
    "prepare" => TokenType::ForPrepare,
    "if" => TokenType::If,
    "else" => TokenType::Else,
    "mix" => TokenType::DoWhileMix,
    "until" => TokenType::DoWhileUntil,
    "serve" => TokenType::PrintServe,
    "plate" => TokenType::ReturnPlate,
    "omelette" => TokenType::StructOmelette,
    "pancake" => TokenType::FunctionPancake,
    "preheat" => TokenType::ForPreheat,
    "at" => TokenType::ForAt,
    "chop" => TokenType::OrChop,
    "blend" => TokenType::AndBlend,
    "taste" => TokenType::EqualEqualTaste,
    "tasteless" => TokenType::LessThanTasteless,
    "tastier" => TokenType::GreaterThanTastier,
    "cookwhile" => TokenType::ForCookUntil,
    "stir" => TokenType::ForStir,
    "ain't" => TokenType::Not,
    "texture" => TokenType::BoolTexture,
    "cal" => TokenType::NumberCal,
    "smoothie" => TokenType::StringSmoothie,
    "empty" => TokenType::VoidEmpty,
};

pub fn lex_tokens(source: String) -> Result<Vec<Token>, LexerError> {
    let mut lexer: Lexer = Default::default();
    lexer.scan_tokens(source);
    match lexer.err {
        Some(err) => Err(err),
        None => Ok(lexer.tokens),
    }
}

pub struct LexerError {
    pub message: String,
    pub line: usize,
    pub col: i64,
}

pub struct Lexer {
    input: Vec<u8>,
    tokens: Vec<Token>,
    start: usize,
    current: usize,
    line: usize,
    col: i64,
    err: Option<LexerError>,
}

impl Default for Lexer {
    fn default() -> Self {
        Lexer {
            input: Vec::new(),
            tokens: Vec::new(),
            start: 0,
            current: 0,
            line: 1,
            col: 0,
            err: None,
        }
    }
}

impl Lexer {
    fn scan_tokens(&mut self, input: String) {
        self.input = input.into_bytes();
        while !self.is_at_end() {
            self.start = self.current;
            self.scan_token();
        }
        self.tokens.push(Token::new(
            TokenType::Eof,
            "".to_string(),
            None,
            self.line,
            self.col,
        ));
    }

    fn scan_token(&mut self) {
        let c = self.advance();
        match c {
            '(' => self.add_token(TokenType::LeftParen),
            ')' => self.add_token(TokenType::RightParen),
            '[' => self.add_token(TokenType::LeftBracket),
            ']' => self.add_token(TokenType::RightBracket),
            '.' => self.add_token(TokenType::Dot),
            ',' => self.add_token(TokenType::Comma),
            '-' => self.add_token(TokenType::Minus),
            '+' => self.add_token(TokenType::Plus),
            '<' => {
                if self.match_char('|') {
                    self.add_token(TokenType::CloseScopeBar);
                } else {
                    self.err = Some(LexerError {
                        message: format!("Expected '|' after '<', got '{}'", self.get_current()),
                        line: self.line,
                        col: self.col,
                    });
                }
            }
            '#' => self.add_token(TokenType::Semicolon),
            '*' => self.add_token(TokenType::Star),
            '/' => {
                if self.match_char('/') {
                    while self.get_current() != '\n' && !self.is_at_end() {
                        self.advance();
                    }
                } else {
                    self.add_token(TokenType::Slash);
                }
            }
            '|' => {
                if self.match_char('>') {
                    self.add_token(TokenType::OpenScopeBar);
                } else {
                    self.err = Some(LexerError {
                        message: format!("Expected '>' after '|', got '{}'", self.get_current()),
                        line: self.line,
                        col: self.col,
                    })
                }
            }
            ':' => self.add_token(TokenType::Colon),
            '"' => self.string(),
            ' ' | '\r' | '\t' => (),
            '\n' => {
                self.line += 1;
                self.col = 0;
            }
            '=' => {
                if self.match_char('=') {
                    if self.match_char('E') {
                        self.add_token(TokenType::AssignFork);
                    } else {
                        self.err = Some(LexerError {
                            message: format!("Unexpected character: {}", self.get_current()),
                            line: self.line,
                            col: self.col,
                        });
                    }
                } else {
                    self.err = Some(LexerError {
                        message: "Invalid assignment syntax".to_string(),
                        line: self.line,
                        col: self.col,
                    });
                }
            }
            _ => {
                if c.is_numeric() {
                    self.number();
                } else if c.is_alphabetic() {
                    self.identifier();
                } else {
                    self.err = Some(LexerError {
                        message: format!("Unexpected character: {}", c),
                        line: self.line,
                        col: self.col,
                    });
                }
            }
        }
    }

    fn string(&mut self) {
        while !self.is_at_end() && self.get_current() != '"' {
            if self.get_current() == '\n' {
                self.line += 1;
            }
            self.advance();
        }
        if self.is_at_end() {
            self.err = Some(LexerError {
                message: "Unterminated string literal.".to_string(),
                col: self.col,
                line: self.line,
            });
        }
        self.advance();
        let value =
            String::from_utf8(self.input[self.start + 1..self.current - 1].to_vec()).unwrap();
        self.add_token_literal(Literal::String(value));
    }

    fn identifier(&mut self) {
        let mut had_single_quote = false;
        while self.get_current().is_alphanumeric() || self.get_current() == '\'' {
            if self.get_current() == '\'' {
                had_single_quote = true;
            }
            self.advance();
        }

        let text = self.get_text();
        if let Some(token_type) = OW_KEYWORDS.get(&text).cloned() {
            self.add_token(token_type);
        } else if !had_single_quote {
            self.add_token_literal(Literal::Identifier(text))
        } else {
            self.err = Some(LexerError {
                message: "Single quotes are not allowed in identifiers".to_string(),
                line: self.line,
                col: self.col,
            })
        }
    }

    fn number(&mut self) {
        while self.get_current().is_ascii_digit() {
            self.advance();
        }

        if self.get_current() == '.' && self.get_next().is_ascii_digit() {
            self.advance();
            while self.get_current().is_digit(10) {
                self.advance();
            }
        }

        let value = String::from_utf8(self.input[self.start..self.current].to_vec()).unwrap();

        match value.parse::<f64>() {
            Ok(num) => self.add_token_literal(Literal::Number(num)),
            Err(_) => {
                self.err = Some(LexerError {
                    message: "Error when parsing number".to_string(),
                    line: self.line,
                    col: self.col,
                })
            }
        }
    }

    fn get_next(&self) -> char {
        if self.current + 1 >= self.input.len() {
            '\0'
        } else {
            char::from(self.input[self.current + 1])
        }
    }

    fn get_current(&self) -> char {
        if self.is_at_end() {
            '\0'
        } else {
            char::from(self.input[self.current])
        }
    }

    fn match_char(&mut self, expected: char) -> bool {
        if !self.is_at_end() && self.get_current() == expected {
            self.advance();
            true
        } else {
            false
        }
    }

    fn add_token(&mut self, token_type: TokenType) {
        let text = self.get_text();
        self.tokens
            .push(Token::new(token_type, text, None, self.line, self.col));
    }

    fn add_token_literal(&mut self, literal: Literal) {
        let text = self.get_text();
        let token_type = match literal {
            Literal::Identifier(_) => TokenType::Identifier,
            Literal::String(_) => TokenType::String,
            Literal::Number(_) => TokenType::Number,
        };

        self.tokens.push(Token::new(
            token_type,
            text,
            Some(literal),
            self.line,
            self.col,
        ));
    }

    fn get_text(&self) -> String {
        String::from_utf8(self.input[self.start..self.current].to_vec()).unwrap()
    }

    fn advance(&mut self) -> char {
        self.current += 1;
        self.col += 1;
        char::from(self.input[self.current - 1])
    }

    fn is_at_end(&self) -> bool {
        self.current >= self.input.len()
    }
}

#[cfg(test)]
mod tests {
    use super::lex_tokens;

    #[test]
    fn test() {
        match lex_tokens(
            "omelette MyStruct |> someFood: smoothie# otherFood: String# <|".to_string(),
        ) {
            Ok(tokens) => {
                println!("{:#?}", tokens);
            }
            Err(err) => {
                panic!(
                    "Error: {} on line {} col {}",
                    err.message, err.line, err.col
                );
            }
        }
    }
}
