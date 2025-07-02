use std::iter::Peekable;

#[derive(Debug, Clone, PartialEq)]
pub enum Token {
    Number(i64),
    Float(f64),
    Str(String),
    Bool(bool),
    Op(String),
    Ident(String),
    Type(String),
    CustomMacroCall(String, Vec<Token>),
    MacroDefine,
    Ref,
    While,
    For,
    In,
    If,
    Else,
    Elif,
    FunctionCall(String, Vec<Token>),
    UnaryMinus,
    PrintLn,
    PrintSingle,
    SuperPrint,
    InputMacro,
    Comma,
    Fn,
    Mut,
    InputOp,
    OutputOp,
    LCurly,
    RCurly,
    Let,
    LParen,
    RParen,
    Colon,
    Semicolon,
    Sleep,
}

#[allow(clippy::to_string_trait_impl)]
impl ToString for Token {
    fn to_string(&self) -> String {
        match self {
            Token::MacroDefine => "@!".to_string(),
            Token::CustomMacroCall(name, args) => {
                let args_str = args
                    .iter()
                    .map(|t| t.to_string())
                    .collect::<Vec<_>>()
                    .join(" ");
                format!("@{}({})", name, args_str)
            }
            Token::FunctionCall(name, args) => {
                let args_str = args
                    .iter()
                    .map(|t| t.to_string())
                    .collect::<Vec<_>>()
                    .join(" ");
                format!("{}({})", name, args_str)
            }
            Token::Sleep => "zzz!".to_string(),
            Token::InputMacro => "inp!()".to_string(),
            Token::PrintSingle => "ps!".to_string(),
            Token::SuperPrint => "sp!".to_string(),
            Token::For => "for".to_string(),
            Token::In => "in".to_string(),
            Token::While => "while".to_string(),
            Token::Elif => "else if".to_string(),
            Token::If => "if".to_string(),
            Token::Else => "else".to_string(),
            Token::Ref => "ref".to_string(),
            Token::UnaryMinus => "-".to_string(),
            Token::LCurly => "{".to_string(),
            Token::RCurly => "}".to_string(),
            Token::Fn => "fn".to_string(),
            Token::Comma => ",".to_string(),
            Token::PrintLn => "p!".to_string(),
            Token::Number(n) => n.to_string(),
            Token::Float(f) => format!("{:?}", f),
            Token::Str(s) => format!("\"{}\"", s),
            Token::Bool(b) => b.to_string(),
            Token::Mut => "&".to_string(),
            Token::Op(op) => op.clone(),
            Token::Ident(ident) => ident.clone(),
            Token::Type(t) => t.clone(),
            Token::InputOp => "->".to_string(),
            Token::OutputOp => "<-".to_string(),
            Token::Let => "v".to_string(),
            Token::LParen => "(".to_string(),
            Token::RParen => ")".to_string(),
            Token::Colon => ":".to_string(),
            Token::Semicolon => ";".to_string(),
        }
    }
}

pub fn combine_tokens<'a, I>(tokens: Peekable<I>) -> String
where
    I: Iterator<Item = &'a Token>,
{
    // Token::Float getting truncated here
    tokens.map(|t| t.to_string()).collect::<Vec<_>>().join("")
}

#[derive(Clone)]
pub struct Lexer {
    pub tokens: Vec<Token>,
}

impl Lexer {
    pub fn new() -> Self {
        Lexer { tokens: Vec::new() }
    }

    pub fn tokenize(&mut self, expr: &str) {
        let mut tokens = Vec::new();
        let mut num = String::new();
        let mut chars = expr.chars().peekable();

        while let Some(&c) = chars.peek() {
            if c.is_whitespace() {
                chars.next();
            } else if c.is_ascii_digit() || c == '.' {
                num.clear();
                let mut has_dot = c == '.';

                if has_dot {
                    num.push('.');
                    chars.next();
                }

                while let Some(&d) = chars.peek() {
                    if d.is_ascii_digit() {
                        num.push(d);
                        chars.next();
                    } else if d == '.' && !has_dot {
                        has_dot = true;
                        num.push(d);
                        chars.next();
                    } else {
                        break;
                    }
                }

                if has_dot {
                    let value = num.parse::<f64>().unwrap();
                    tokens.push(Token::Float(value));
                } else {
                    let value = num.parse::<i64>().unwrap();
                    tokens.push(Token::Number(value));
                }
            } else if c == '<' {
                chars.next();
                if chars.peek() == Some(&'-') {
                    tokens.push(Token::OutputOp);
                    chars.next();
                } else {
                    tokens.push(Token::Op("<".to_string()));
                }
            } else if c == '-' {
                chars.next();

                if chars.peek() == Some(&'>') {
                    tokens.push(Token::InputOp);
                    chars.next();
                } else {
                    let prev = tokens.last();

                    let is_unary =
                        prev.is_none() || matches!(prev, Some(Token::Op(_)) | Some(Token::LParen));
                    if is_unary {
                        let mut has_dot = c == '.';

                        num.clear();
                        num.push('-');

                        if has_dot {
                            num.push('.');
                            chars.next();
                        }

                        while let Some(&d) = chars.peek() {
                            if d.is_ascii_digit() {
                                num.push(d);
                                chars.next();
                            } else if d == '.' && !has_dot {
                                has_dot = true;
                                num.push(d);
                                chars.next();
                            } else {
                                break;
                            }
                        }

                        while let Some(&d) = chars.peek() {
                            if d.is_ascii_digit() {
                                num.push(d);
                                chars.next();
                            } else {
                                break;
                            }
                        }
                        if has_dot {
                            match num.parse::<f64>() {
                                Ok(v) => tokens.push(Token::Float(v)),
                                Err(_) => {
                                    tokens.push(Token::UnaryMinus);
                                }
                            }
                        } else if let Ok(v) = num.parse::<i64>() {
                            tokens.push(Token::Number(v))
                        }
                    } else {
                        tokens.push(Token::Op("-".to_string()));
                    }
                }
            } else if c == '"' {
                chars.next(); // skip opening "
                let mut string = String::new();
                let mut expecting_escape_end = false;
                while let Some(&ch) = chars.peek() {
                    if ch == '"' && !expecting_escape_end {
                        break;
                    }
                    if expecting_escape_end {
                        expecting_escape_end = false;
                    }
                    if ch == '\\' {
                        expecting_escape_end = true;
                    }
                    string.push(ch);
                    chars.next();
                }
                chars.next(); // skip closing "
                tokens.push(Token::Str(string));
            } else if c == '@' {
                chars.next();

                let mut is_def = false;
                if let Some(e) = chars.peek() {
                    if e == &'!' {
                        is_def = true;
                        tokens.push(Token::MacroDefine);
                        chars.next();
                    }
                }

                if !is_def {
                    let mut word = String::new();
                    while let Some(&ch) = chars.peek() {
                        if ch.is_alphanumeric() || ch == '_' {
                            word.push(ch);
                            chars.next();
                        } else {
                            break;
                        }
                    }

                    let mut paren_depth = 1;
                    let mut temp = String::new();

                    for ch in chars.by_ref() {
                        match ch {
                            '(' => {
                                paren_depth += 1;
                                temp.push(ch);
                            }
                            ')' => {
                                paren_depth -= 1;
                                if paren_depth == 0 {
                                    break;
                                } else {
                                    temp.push(ch);
                                }
                            }
                            _ => temp.push(ch),
                        }
                    }

                    let mut arg_lexer = Lexer { tokens: vec![] };
                    arg_lexer.tokenize(&temp);
                    tokens.push(Token::CustomMacroCall(word, arg_lexer.tokens.clone()));
                } else {
                    let mut word = String::new();
                    while let Some(&ch) = chars.peek() {
                        if ch.is_alphanumeric() || ch == '_' {
                            word.push(ch);
                            chars.next();
                        } else {
                            break;
                        }
                    }

                    tokens.push(Token::Ident(word));

                    if c == '<' {
                        chars.next();
                        if chars.peek() == Some(&'-') {
                            tokens.push(Token::OutputOp);
                            chars.next();
                        }
                    }

                    let mut string = String::new();
                    if c == '"' {
                        chars.next(); // skip opening "
                        while let Some(&ch) = chars.peek() {
                            if ch == '"' {
                                break;
                            }
                            string.push(ch);
                            chars.next();
                        }
                        chars.next(); // skip closing "
                        tokens.push(Token::Str(string));
                    }
                }
            } else if c.is_alphabetic() || c == '_' {
                let mut word = String::new();
                while let Some(&ch) = chars.peek() {
                    if ch.is_alphanumeric() || ch == '_' {
                        word.push(ch);
                        chars.next();
                    } else {
                        break;
                    }
                }

                // Identifiers and keywords
                match word.as_str() {
                    "v" => tokens.push(Token::Let),
                    "p" => {
                        if let Some(&'!') = chars.peek() {
                            chars.next();
                            tokens.push(Token::PrintLn);
                        }
                    }
                    "inp" => {
                        if let Some(&'!') = chars.peek() {
                            chars.next();
                            if let Some(&'(') = chars.peek() {
                                chars.next();
                                if let Some(&')') = chars.peek() {
                                    tokens.push(Token::InputMacro);
                                }
                            }
                        }
                    }
                    "ps" => {
                        if let Some(&'!') = chars.peek() {
                            chars.next();
                            tokens.push(Token::PrintSingle);
                        }
                    }
                    "sp" => {
                        if let Some(&'!') = chars.peek() {
                            chars.next();
                            tokens.push(Token::SuperPrint);
                        }
                    }
                    "zzz" => {
                        if let Some(&'!') = chars.peek() {
                            chars.next();
                            tokens.push(Token::Sleep);
                        }
                    }
                    //"elif" => tokens.push(Token::Elif),
                    "ref" => tokens.push(Token::Ref),
                    "while" => tokens.push(Token::While),
                    "fn" => tokens.push(Token::Fn),
                    "if" => tokens.push(Token::If),
                    "for" => tokens.push(Token::For),
                    "in" => tokens.push(Token::In),
                    "else" => {
                        let mut word2 = String::new();
                        while let Some(&ch) = chars.peek() {
                            if ch.is_alphanumeric() {
                                if word2.as_str() == "if" {
                                    break;
                                }
                                word2.push(ch);
                                chars.next();
                            } else if ch == ' ' {
                                chars.next();
                            } else {
                                break;
                            }
                        }

                        if word2.as_str() == "if" {
                            tokens.push(Token::Elif)
                        } else {
                            tokens.push(Token::Else)
                        }
                    }
                    "true" => tokens.push(Token::Bool(true)),
                    "false" => tokens.push(Token::Bool(false)),
                    "int" | "bool" | "str" | "float" => tokens.push(Token::Type(word)),
                    _ => {
                        if let Some(&'(') = chars.peek() {
                            chars.next();

                            let mut paren_depth = 1;
                            let mut temp = String::new();

                            for ch in chars.by_ref() {
                                match ch {
                                    '(' => {
                                        paren_depth += 1;
                                        temp.push(ch);
                                    }
                                    ')' => {
                                        paren_depth -= 1;
                                        if paren_depth == 0 {
                                            break;
                                        } else {
                                            temp.push(ch);
                                        }
                                    }
                                    _ => temp.push(ch),
                                }
                            }

                            let mut arg_lexer = Lexer { tokens: vec![] };
                            arg_lexer.tokenize(&temp);
                            tokens.push(Token::FunctionCall(word, arg_lexer.tokens.clone()));
                        } else {
                            tokens.push(Token::Ident(word));
                        }
                    }
                }
            } else {
                let mut op = String::new();
                op.push(c);
                chars.next();

                if let Some(&next) = chars.peek() {
                    let combo = format!("{}{}", op, next);
                    if matches!(combo.as_str(), "//") {
                        chars.next();
                        for ch in chars.by_ref() {
                            if ch == '\n' {
                                break;
                            }
                        }
                        continue;
                    }
                    if matches!(combo.as_str(), "/*") {
                        chars.next(); // consume '*'
                        while let Some(c) = chars.next() {
                            if c == '*' && *chars.peek().unwrap() == '/' {
                                chars.next(); // consume '/'
                                break;
                            }
                        }
                        continue; // skip comment
                    }
                    if matches!(combo.as_str(), "::" | "!:" | "&&" | "||" | ">:" | "<:") {
                        chars.next();
                        op = combo;
                    }
                }

                match op.as_str() {
                    "+" | "*" | "/" | "%" | "::" | "!:" | ">" | "<" | ">:" | "<:" | "&&" | "||"
                    | "!" => {
                        tokens.push(Token::Op(op));
                    }
                    "{" => tokens.push(Token::LCurly),
                    "}" => tokens.push(Token::RCurly),
                    "," => tokens.push(Token::Comma),
                    "(" => tokens.push(Token::LParen),
                    ")" => tokens.push(Token::RParen),
                    ":" => tokens.push(Token::Colon),
                    ";" => tokens.push(Token::Semicolon),
                    "&" => tokens.push(Token::Mut),
                    _ => panic!("Unknown operator: {}", op),
                }
            }
        }

        self.tokens = tokens;
    }
}
