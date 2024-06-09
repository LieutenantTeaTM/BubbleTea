// This file handles parsing BubbleTea

// Much of the base source code was lifted from the nano_rust example for chumsky!

// For error formatting. Makes it look pretty!
use ariadne::{sources, Config, Label, Report, ReportKind};
// For easy parsers. Check this project out! 
use chumsky::prelude::*;
// Rust std libs
use std::{collections::HashMap, env, fmt, fs, str};
use std::time::Duration;
use std::thread::sleep;
use rand::Rng;
use std::process::Command;

// Creates a span for the parser
pub type Span = SimpleSpan<usize>;


// Enum for all known tokens. Note these have to be defined later
#[derive(Clone, Debug, PartialEq)]
pub enum Token<'src> {
    // "Null" or non value
    // Token value can be defined as "null"
    Null,

    // Binary value for "true" or "false" respectively
    Bool(bool),

    // Can be used in math or variables (floar or int)
    Num(f64),

    // Rudimentary string system. Defined between ""
    // Can be used as variables
    // Concat with "|"
    Str(&'src str),

    // ::, !:. +, -, *, / etc.
    Op(&'src str),

    // Ctrl operators for one of tokens
    // : ; [ ] { } ; etc.
    // BubbleTea uses EOL (end of line) syntax with ;
    Ctrl(char),

    // Variable names
    Ident(&'src str),

    App,

    // Function declaration (fn)
    Fn,

    Fidx,

    // Equivalent to rust's let, "v", short for var.
    Let,

    Assign,

    DefStr,

    DefNum,

    Len,

    SleepStr,

    Flush,
    
    // Another staple of BubbleTea, "p" short for print. Prints whatever value as you'd expect
    // declared like p(value);
    Print,

    PrintLine,

    InputBuf,

    // Simple if
    If,
    
    // Simple else. Also works as an else if as needed
    Else,

    For,

    In,

    Idx,

    RemIdx,

    RepIdx,
    
    Rng,

    Round,

    While,

    Break,
}

// Impl for tokens, used in parsing
impl<'src> fmt::Display for Token<'src> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // Formats tokens and pushes them to the buffer
        match self {
            Token::Null => write!(f, "null"),
            Token::Bool(x) => write!(f, "{}", x),
            Token::Num(n) => write!(f, "{}", n),
            Token::Str(s) => write!(f, "{}", s),
            Token::Op(s) => write!(f, "{}", s),
            Token::Ctrl(c) => write!(f, "{}", c),
            Token::Ident(s) => write!(f, "{}", s),
            Token::App => write!(f, "app"),
            Token::Fn => write!(f, "fn"),
            Token::Let => write!(f, "v"),
            Token::Assign => write!(f, "vup"),
            Token::Flush => write!(f, "flush"),
            Token::DefStr => write!(f, "str"),
            Token::DefNum => write!(f, "num"),
            Token::SleepStr => write!(f, "sleep"),
            Token::Fidx => write!(f, "fidx"),
            Token::Idx => write!(f, "idx"),
            Token::RemIdx => write!(f, "rem_idx"),
            Token::RepIdx => write!(f, "rep_idx"),
            Token::Rng => write!(f, "rng"),
            Token::Round => write!(f, "round"),
            Token::Len => write!(f, "len"),
            Token::Print => write!(f, "p"),
            Token::PrintLine => write!(f, "pln"),
            Token::InputBuf => write!(f, "inp"),
            Token::For => write!(f, "for"),
            Token::In => write!(f, "in"),
            Token::If => write!(f, "if"),
            Token::Else => write!(f, "else"),
            Token::While => write!(f, "while"),
            Token::Break => write!(f, "break"),
        }
    }
}

fn lexer<'src>(
) -> impl Parser<'src, &'src str, Vec<(Token<'src>, Span)>, extra::Err<Rich<'src, char, Span>>> {
    // A parser for numbers
    let num = just('-').or_not().then(text::int(10))
        .then(just('.').then(text::digits(10)).or_not())
        .to_slice()
        .from_str()
        .unwrapped()
        .map(Token::Num);

    // A parser for strings
    let str_ = just('"')
        .ignore_then(none_of('"').repeated())
        .then_ignore(just('"'))
        .to_slice()
        .map(|s: &str| Token::Str(&str::from_utf8(&s.as_bytes()[1..s.len() - 1]).unwrap()));


    // A parser for operators
    let op = one_of("+*-/><!:&|")
        .repeated()
        .at_least(1)
        .to_slice()
        .map(Token::Op);

    // A parser for control characters (delimiters, semicolons, etc.)
    let ctrl = one_of("()[]{};,").map(Token::Ctrl);

    // A parser for identifiers and keywords
    let ident = text::ascii::ident().map(|ident: &str| match ident {
        "fn" => Token::Fn,
        "app" => Token::App,
        "fidx" => Token::Fidx,
        "v" => Token::Let,
        "vup" => Token::Assign,
        "str" => Token::DefStr,
        "idx" => Token::Idx,
        "rem_idx" => Token::RemIdx,
        "rep_idx" => Token::RepIdx,
        "rng" => Token::Rng,
        "round" => Token::Round,
        "num" => Token::DefNum,
        "flush" => Token::Flush,
        "len" => Token::Len,
        "sleep" => Token::SleepStr,
        "p" => Token::Print,
        "pln" => Token::PrintLine,
        "inp" => Token::InputBuf,
        "if" => Token::If,
        "for" => Token::For,
        "while" => Token::While,
        "break" => Token::Break,
        "in" => Token::In,
        "else" => Token::Else,
        "true" => Token::Bool(true),
        "false" => Token::Bool(false),
        "null" => Token::Null,
        _ => Token::Ident(ident),
    });

    // A single token can be one of the above
    let token = num.or(str_).or(op).or(ctrl).or(ident);

    // Parse for comments "//"
    let comment = just("//")
        .then(any().and_is(just("\n").not()).repeated())
        .padded();

    // Parsing tokens
    token
        .map_with(|tok, e| (tok, e.span()))
        .padded_by(comment.repeated())
        .padded()
        // If we encounter an error, skip and attempt to lex the next character as a token instead
        .recover_with(skip_then_retry_until(any().ignored(), end()))
        .repeated()
        .collect()
}

// Values for expression parsing
#[derive(Clone, Debug, PartialEq)]
enum Value<'src> {
    // Data types in BubbleTea
    Null,
    Bool(bool),
    Num(f64),
    Str(&'src str),
    List(Vec<Self>),
    Func(&'src str),
    Break,
}

impl<'src> Value<'src> {
    // Checks if a number in BubbleTea is a number
    fn num(self, span: Span) -> Result<f64, Error> {
        if let Value::Num(x) = self {
            Ok(x)
        } else {
            Err(Error {
                span,
                msg: format!("'{}' is not a number", self),
            })
        }
    }
}

impl<'src> std::fmt::Display for Value<'src> {
    // Formatting data types
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Self::Null => write!(f, "null"),
            Self::Bool(x) => write!(f, "{}", x),
            Self::Num(x) => write!(f, "{}", x),
            Self::Str(x) => write!(f, "{}", x),
            Self::List(xs) => write!(
                f,
                "[{}]",
                xs.iter()
                    .map(|x| x.to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            Self::Func(name) => write!(f, "<function: {}>", name),
            Self::Break => write!(f, "break"),
        }
    }
}

#[derive(Clone, Debug)]
enum BinaryOp {
    // All binary operator tokens
    Concat,
    Add,
    Sub,
    Mul,
    Div,
    GreaterThan,
    LessThan,
    GreaterEq,
    LessEq,
    Eq,
    NotEq,
    And,
    Or,
}

pub type Spanned<T> = (T, Span);

// An expression node in the AST. Children are spanned so we can generate useful runtime errors.
#[derive(Debug)]
enum Expr<'src> {
    Error,
    Value(Value<'src>),
    App(Vec<Spanned<Self>>),
    Fidx(Vec<Spanned<Self>>),
    List(Vec<Spanned<Self>>),
    Local(&'src str),
    Let(&'src str, Box<Spanned<Self>>, Box<Spanned<Self>>),
    Assign(&'src str, Box<Spanned<Self>>, Box<Spanned<Self>>),
    DefStr(Box<Spanned<Self>>),
    Flush(Box<Spanned<Self>>),
    DefNum(Box<Spanned<Self>>),
    Idx(Vec<Spanned<Self>>),
    RemIdx(Vec<Spanned<Self>>),
    RepIdx(Vec<Spanned<Self>>),
    Rng(Vec<Spanned<Self>>),
    Round(Box<Spanned<Self>>),
    Len(Box<Spanned<Self>>),
    InputBuf(Box<Spanned<Self>>),
    Then(Box<Spanned<Self>>, Box<Spanned<Self>>),
    Binary(Box<Spanned<Self>>, BinaryOp, Box<Spanned<Self>>),
    Call(Box<Spanned<Self>>, Spanned<Vec<Spanned<Self>>>),
    If(Box<Spanned<Self>>, Box<Spanned<Self>>, Box<Spanned<Self>>),
    SleepStr(Box<Spanned<Self>>),
    Print(Box<Spanned<Self>>),
    PrintLine(Box<Spanned<Self>>),
    ForLoop(&'src str, Box<Spanned<Self>>, Box<Spanned<Self>>),
    WhileLoop(Box<Spanned<Self>>, Box<Spanned<Self>>),
    Break
}

// A function node in the AST.
#[derive(Debug)]
struct Func<'src> {
    args: Vec<&'src str>,
    span: Span,
    body: Spanned<Expr<'src>>,
}

// The type of the input that our parser operates on. The input is the `&[(Token, Span)]` token buffer generated by the
// lexer, wrapped in a `SpannedInput` which 'splits' it apart into its constituent parts, tokens and spans, for chumsky
// to understand.
type ParserInput<'tokens, 'src> =
    chumsky::input::SpannedInput<Token<'src>, Span, &'tokens [(Token<'src>, Span)]>;

// Parser for expressions
fn expr_parser<'tokens, 'src: 'tokens>() -> impl Parser<
    'tokens,
    ParserInput<'tokens, 'src>,
    Spanned<Expr<'src>>,
    extra::Err<Rich<'tokens, Token<'src>, Span>>,
> + Clone {
    recursive(|expr| {
        let inline_expr = recursive(|inline_expr| {
            let val = select! {
                Token::Null => Expr::Value(Value::Null),
                Token::Bool(x) => Expr::Value(Value::Bool(x)),
                Token::Num(n) => Expr::Value(Value::Num(n)),
                Token::Str(s) => Expr::Value(Value::Str(s)),
            }
            .labelled("value");

            let ident = select! { Token::Ident(ident) => ident }.labelled("identifier");
            // A list of expressions
            let items = expr
                .clone()
                .separated_by(just(Token::Ctrl(',')))
                .allow_trailing()
                .collect::<Vec<_>>();

            // A let expression
            let let_ = just(Token::Let)
                .ignore_then(ident)
                .then_ignore(just(Token::Op(":")))
                .then(inline_expr.clone())
                .then_ignore(just(Token::Ctrl(';')))
                .then(expr.clone())
                .map(|((name, val), body)| Expr::Let(name, Box::new(val), Box::new(body)));

            let append_ = just(Token::App)
                .ignore_then(
                    items
                    .clone()
                    .map(Expr::App)
                    .delimited_by(just(Token::Ctrl('(')), just(Token::Ctrl(')'))));

            let assign = just(Token::Assign)
                .ignore_then(ident)
                .then_ignore(just(Token::Op(":")))
                .then(inline_expr.clone())
                .then_ignore(just(Token::Ctrl(';')))
                .then(expr.clone())
                .map(|((name, val), body)| Expr::Assign(name, Box::new(val), Box::new(body)));

            let break_ = just(Token::Break)
                .then_ignore(just(Token::Ctrl(';')))
                .then(expr.clone())
                .map(|_ | Expr::Break);

            let fidx = just(Token::Fidx)
                .ignore_then(
                    items
                    .clone()
                    .map(Expr::Fidx)
                    .delimited_by(just(Token::Ctrl('(')), just(Token::Ctrl(')'))));

            let list = items
                .clone()
                .map(Expr::List)
                .delimited_by(just(Token::Ctrl('[')), just(Token::Ctrl(']')));

            let idx = just(Token::Idx)
                .ignore_then(
                    items
                    .clone()
                    .map(Expr::Idx)
                    .delimited_by(just(Token::Ctrl('(')), just(Token::Ctrl(')'))));

            let rem_idx = just(Token::RemIdx)
                    .ignore_then(
                        items
                        .clone()
                        .map(Expr::RemIdx)
                        .delimited_by(just(Token::Ctrl('(')), just(Token::Ctrl(')'))));
                    
            let rep_idx = just(Token::RepIdx)
                    .ignore_then(
                        items
                        .clone()
                        .map(Expr::RepIdx)
                        .delimited_by(just(Token::Ctrl('(')), just(Token::Ctrl(')'))));

            let rng_ = just(Token::Rng)
                        .ignore_then(
                            items
                            .clone()
                            .map(Expr::Rng)
                            .delimited_by(just(Token::Ctrl('(')), just(Token::Ctrl(')'))));

            // 'Atoms' are expressions that contain no ambiguity
            let atom = val
                .or(ident.map(Expr::Local))
                .or(let_)
                .or(append_)
                .or(fidx)
                .or(assign)
                .or(break_)
                .or(list)
                .or(idx)
                .or(rem_idx)
                .or(rep_idx)
                .or(rng_)
                //.or(atom_choice)
                .or(just(Token::Round)
                    .ignore_then(
                        expr.clone()
                            .delimited_by(just(Token::Ctrl('(')), just(Token::Ctrl(')'))),
                    )
                .map(|expr| Expr::Round(Box::new(expr))))
                .or(just(Token::DefStr)
                    .ignore_then(
                        expr.clone()
                            .delimited_by(just(Token::Ctrl('(')), just(Token::Ctrl(')'))),
                    )
                .map(|expr| Expr::DefStr(Box::new(expr))))
                .or(just(Token::DefNum)
                    .ignore_then(
                        expr.clone()
                            .delimited_by(just(Token::Ctrl('(')), just(Token::Ctrl(')'))),
                    )
                .map(|expr| Expr::DefNum(Box::new(expr))))
                .or(just(Token::Flush)
                    .ignore_then(
                        expr.clone()
                            .delimited_by(just(Token::Ctrl('(')), just(Token::Ctrl(')'))),
                    )
                    .map(|expr| Expr::Flush(Box::new(expr))))
                .or(just(Token::Len)
                    .ignore_then(
                        expr.clone()
                            .delimited_by(just(Token::Ctrl('(')), just(Token::Ctrl(')'))),
                    )
                .map(|expr| Expr::Len(Box::new(expr))))
                .or(just(Token::SleepStr)
                    .ignore_then(
                        expr.clone()
                            .delimited_by(just(Token::Ctrl('(')), just(Token::Ctrl(')')))
                    )
                    .map(|expr| Expr::SleepStr(Box::new(expr))))
                .or(just(Token::Print)
                    .ignore_then(
                        expr.clone()
                            .delimited_by(just(Token::Ctrl('(')), just(Token::Ctrl(')')))
                    )
                    .map(|expr| Expr::Print(Box::new(expr))))
                .or(just(Token::PrintLine)
                    .ignore_then(
                        expr.clone()
                            .delimited_by(just(Token::Ctrl('(')), just(Token::Ctrl(')')))
                    )
                    .map(|expr| Expr::PrintLine(Box::new(expr))))
                .or(just(Token::InputBuf)
                    .ignore_then(
                        expr.clone()
                            .delimited_by(just(Token::Ctrl('(')), just(Token::Ctrl(')')))
                    )
                    .map(|expr| Expr::InputBuf(Box::new(expr))))
                .map_with(|expr, e| (expr, e.span()))
                // Atoms can also just be normal expressions, but surrounded with parentheses
                .or(expr
                    .clone()
                    .delimited_by(just(Token::Ctrl('(')), just(Token::Ctrl(')'))))
                // Attempt to recover anything that looks like a parenthesised expression but contains errors
                .recover_with(via_parser(nested_delimiters(
                    Token::Ctrl('('),
                    Token::Ctrl(')'),
                    [
                        (Token::Ctrl('['), Token::Ctrl(']')),
                        (Token::Ctrl('{'), Token::Ctrl('}')),
                    ],
                    |span| (Expr::Error, span),
                )))
                // Attempt to recover anything that looks like a list but contains errors
                .recover_with(via_parser(nested_delimiters(
                    Token::Ctrl('['),
                    Token::Ctrl(']'),
                    [
                        (Token::Ctrl('('), Token::Ctrl(')')),
                        (Token::Ctrl('{'), Token::Ctrl('}')),
                    ],
                    |span| (Expr::Error, span),
                )))
                .boxed();

            // Function calls have very high precedence so we prioritise them
            let call = atom.foldl_with(
                items
                    .delimited_by(just(Token::Ctrl('(')), just(Token::Ctrl(')')))
                    .map_with(|args, e| (args, e.span()))
                    .repeated(),
                |f, args, e| (Expr::Call(Box::new(f), args), e.span()),
            );

            let op = 
                just(Token::Op("|"))
                .to(BinaryOp::Concat);

            let cc_compare = call.clone()
                .clone()
                .foldl_with(op.then(call.clone()).repeated(), |a, (op, b), e| {
                    (Expr::Binary(Box::new(a), op, Box::new(b)), e.span())
                });

            // Product ops (multiply and divide) have equal precedence
            let op = just(Token::Op("*"))
                .to(BinaryOp::Mul)
                .or(just(Token::Op("/")).to(BinaryOp::Div));
            let product = cc_compare
                .clone()
                .foldl_with(op.then(cc_compare).repeated(), |a, (op, b), e| {
                    (Expr::Binary(Box::new(a), op, Box::new(b)), e.span())
                });

            // Sum ops (add and subtract) have equal precedence
            let op = just(Token::Op("+"))
                .to(BinaryOp::Add)
                .or(just(Token::Op("-")).to(BinaryOp::Sub));
            let sum = product
                .clone()
                .foldl_with(op.then(product).repeated(), |a, (op, b), e| {
                    (Expr::Binary(Box::new(a), op, Box::new(b)), e.span())
                });

            // Greater than/Less than
            let op = just(Token::Op(">"))
            .to(BinaryOp::GreaterThan)
            .or(just(Token::Op("<")).to(BinaryOp::LessThan));
            let gt_or_lt = sum
                .clone()
                .foldl_with(op.then(sum).repeated(), |a, (op, b), e| {
                    (Expr::Binary(Box::new(a), op, Box::new(b)), e.span())
                });

            let op = just(Token::Op(">:"))
                .to(BinaryOp::GreaterEq)
                .or(just(Token::Op("<:")).to(BinaryOp::LessEq));
            let ge_or_le = gt_or_lt
                    .clone()
                    .foldl_with(op.then(gt_or_lt).repeated(), |a, (op, b), e| {
                        (Expr::Binary(Box::new(a), op, Box::new(b)), e.span())
                    });

            // Comparison ops (equal, not-equal) have equal precedence
            let op = just(Token::Op("::"))
                .to(BinaryOp::Eq)
                .or(just(Token::Op("!:")).to(BinaryOp::NotEq));
            let compare = ge_or_le
                .clone()
                .foldl_with(op.then(ge_or_le).repeated(), |a, (op, b), e| {
                    (Expr::Binary(Box::new(a), op, Box::new(b)), e.span())
                });

            let op = just(Token::Op("&&"))
                .to(BinaryOp::And)
                .or(just(Token::Op("||")).to(BinaryOp::Or));
            let and_or = compare
                .clone()
                .foldl_with(op.then(compare).repeated(), |a, (op, b), e| {
                    (Expr::Binary(Box::new(a), op, Box::new(b)), e.span())
                });

            and_or.labelled("expression").as_context()
        });

        // Blocks are expressions but delimited with braces
        let block = expr
            .clone()
            .delimited_by(just(Token::Ctrl('{')), just(Token::Ctrl('}')))
            // Attempt to recover anything that looks like a block but contains errors
            .recover_with(via_parser(nested_delimiters(
                Token::Ctrl('{'),
                Token::Ctrl(';'),
                [
                    (Token::Ctrl('('), Token::Ctrl(';')),
                    (Token::Ctrl('['), Token::Ctrl(';')),
                ],
                |span| (Expr::Error, span),
            )))
            .boxed();

        let if_: Recursive<dyn Parser<_, (Expr, SimpleSpan), _>> = recursive(|if_| {
            just(Token::If)
                .ignore_then(expr.clone())
                .then(block.clone())
                .then(
                    just(Token::Else)
                        .ignore_then(block.clone().or(if_))
                        .or_not(),
                )
                .map_with(|((cond, in_var), b), e| {
                    (
                        Expr::If(
                            Box::new(cond),
                            Box::new(in_var),
                            // If an `if` expression has no trailing `else` block, we magic up one that just produces null
                            Box::new(b.unwrap_or_else(|| (Expr::Value(Value::Null), e.span()))),
                        ),
                        e.span(),
                    )
                })
        });

        
        let for_: Recursive<dyn Parser<_, (Expr, SimpleSpan), _>> = recursive(|_for_| {
            just(Token::For)
            .ignore_then(select! {
                Token::Ident(ident) => ident,
            })
            .then_ignore(just(Token::In))
            .then(expr.clone())
            .then(block.clone())
            .map_with(|((var, iterable), body), span| {
                (
                    Expr::ForLoop(
                        var,
                        Box::new(iterable),
                        Box::new(body),
                    ),
                    span.span(),
                )
            })
        });

        let while_: Recursive<dyn Parser<_, (Expr, SimpleSpan), _>> = recursive(|_while_| {
            just(Token::While)
                .ignore_then(expr.clone())
                .then(block.clone())
                .map_with(|(cond, b), e| {
                    (
                        Expr::WhileLoop(
                            Box::new(cond),
                            Box::new(b),
                        ),
                        e.span(),
                    )
                })
        });

        let block_expr = block.or(if_).or(for_).or(while_);

        let block_chain = block_expr
            .clone()
            .foldl_with(block_expr.clone().repeated(), |a, b, e| {
                (Expr::Then(Box::new(a), Box::new(b)), e.span())
            });

        let block_recovery = nested_delimiters(
            Token::Ctrl('{'),
            Token::Ctrl('}'),
            [
                (Token::Ctrl('('), Token::Ctrl(')')),
                (Token::Ctrl('['), Token::Ctrl(']')),
            ],
            |span| (Expr::Error, span),
        )
        .boxed();

        block_chain
            .labelled("block")
            // Expressions, chained by semicolons, are statements
            .or(inline_expr.clone())
            .recover_with(skip_then_retry_until(
                block_recovery.ignored().or(any().ignored()),
                one_of([
                    Token::Ctrl(';'),
                    Token::Ctrl('}'),
                    Token::Ctrl(')'),
                    Token::Ctrl(']'),
                ])
                .ignored(),
            ))
            .foldl_with(
                just(Token::Ctrl(';')).ignore_then(expr.or_not()).repeated(),
                |a, b, e| {
                    let span: Span = e.span();
                    (
                        Expr::Then(
                            Box::new(a),
                            // If there is no b expression then its span is the end of the statement/block.
                            Box::new(
                                b.unwrap_or_else(|| (Expr::Value(Value::Null), span.to_end())),
                            ),
                ),
                        span,
                    )
                },
            ).boxed()
    })
}

// Function parser
fn funcs_parser<'tokens, 'src: 'tokens>() -> impl Parser<
    'tokens,
    ParserInput<'tokens, 'src>,
    HashMap<&'src str, Func<'src>>,
    extra::Err<Rich<'tokens, Token<'src>, Span>>,
> + Clone {
    let ident = select! { Token::Ident(ident) => ident }.boxed();

    // Argument lists are just identifiers separated by commas, surrounded by parentheses
    let args = ident.clone()
        .separated_by(just(Token::Ctrl(',')))
        .allow_trailing()
        .collect()
        .delimited_by(just(Token::Ctrl('(')), just(Token::Ctrl(')')))
        .labelled("function args")
        .boxed();



    let func = just(Token::Fn)
        .ignore_then(
            ident
                .map_with(|name, e| (name, e.span()))
                .labelled("function name"),
        )
        .then(args)
        .map_with(|start, e| (start, e.span()))
        .then(
            expr_parser()
                .delimited_by(just(Token::Ctrl('{')), just(Token::Ctrl('}')))
                // Attempt to recover anything that looks like a function body but contains errors
                .recover_with(via_parser(nested_delimiters(
                    Token::Ctrl('{'),
                    Token::Ctrl('}'),
                    [
                        (Token::Ctrl('('), Token::Ctrl(')')),
                        (Token::Ctrl('['), Token::Ctrl(']')),
                    ],
                    |span| (Expr::Error, span),
                ))),
        )
        .map(|(((name, args), span), body)| (name, Func { args, span, body }))
        .labelled("function")
        .boxed();

    func.repeated()
        .collect::<Vec<_>>()
        .validate(|fs, _, emitter| {
            let mut funcs = HashMap::new();
            for ((name, name_span), f) in fs {
                if funcs.insert(name, f).is_some() {
                    emitter.emit(Rich::custom(
                        name_span,
                        format!("Function '{}' already exists", name),
                    ));
                }
            }
            funcs
        }).boxed()
}

struct Error {
    span: Span,
    msg: String,
}

// For unboxing some data
fn char_to_str_converter<'src>(c: char) -> &'src str {
    let s: String = c.to_string();
    Box::leak(s.into_boxed_str())
}

fn string_to_str_converter<'src>(c: String) -> &'src str {
    let s: String = c.to_string();
    Box::leak(s.into_boxed_str())
}

#[allow(dead_code)]
#[cfg(target_os = "windows")]
fn clear_screen() {
    Command::new("cmd")
        .args(&["/C", "cls"])
        .status()
        .unwrap();
}

#[allow(dead_code)]
#[cfg(any(target_os = "linux", target_os = "macos"))]
fn clear_screen() {
    Command::new("clear")
        .status()
        .unwrap();
}

// Evaluate gathered expressions
fn eval_expr<'src>(
    expr: &Spanned<Expr<'src>>,
    funcs: &HashMap<&'src str, Func<'src>>,
    stack: &mut Vec<(&'src str, Value<'src>)>,
) -> Result<Value<'src>, Error> {
    Ok(match &expr.0 {
        Expr::Error => unreachable!(),
        Expr::Value(val) => val.clone(),
        Expr::List(items) => Value::List(
            items
                .iter()
                .map(|item| eval_expr(item, funcs, stack))
                .collect::<Result<_, _>>()?,
        ),
        Expr::Local(name) => stack
            .iter()
            .rev()
            .find(|(l, _)| l == name)
            .map(|(_, v)| v.clone())
            .or_else(|| Some(Value::Func(name)).filter(|_| funcs.contains_key(name)))
            .ok_or_else(|| Error {
                span: expr.1,
                msg: format!("No such variable '{}' in scope", name),
            })?,
        Expr::Let(local, val, body) => {
            let val = eval_expr(val, funcs, stack)?;
            stack.push((local, val));
            let res = eval_expr(body, funcs, stack)?;
            stack.pop();
            res
        }
        Expr::App(items) => Value::List({
            if items.len() != 2 {
                return Err(Error {
                    span: items[0].1, 
                    msg: format!("Wrong number of args (expected 2)"),
                });
            } else {
                let arg1 = eval_expr(&items[0], funcs, stack)?;
                let arg2 = eval_expr(&items[1], funcs, stack)?;
                if let Value::List(mut l) = arg1 {
                    l.push(arg2.clone());
                    l.clone()
                } else {
                    return Err(Error {
                        span: items[0].1, 
                        msg: format!("Arg 1 must be a list"),
                    });
                }
            }
        }),
        Expr::Assign(local, val, body) => {
            let new_val = eval_expr(val, funcs, stack)?;
            if let Some(_var) = stack.iter_mut().rev().find(|(l, _)| l == local) {
                stack.push((local, new_val));
                let res = eval_expr(body, funcs, stack)?;
                res
            } else {
                return Err(Error {
                    span: expr.1, // Update span handling as needed
                    msg: format!("No such variable '{}' in scope", local),
                });
            }
        }
        Expr::Then(a, b) => {
            eval_expr(a, funcs, stack)?;
            eval_expr(b, funcs, stack)?
        }
        Expr::Binary(a, BinaryOp::Concat, b) => Value::Str({
            let val1: Value<'_> = eval_expr(a, funcs, stack)?;
            let val2: Value<'_> = eval_expr(b, funcs, stack)?;
            let val: String = val1.to_string() + &val2.to_string();
            val.leak()
        }),
        Expr::Binary(a, BinaryOp::Add, b) => Value::Num(
            eval_expr(a, funcs, stack)?.num(a.1)? + eval_expr(b, funcs, stack)?.num(b.1)?,
        ),
        Expr::Binary(a, BinaryOp::Sub, b) => Value::Num(
            eval_expr(a, funcs, stack)?.num(a.1)? - eval_expr(b, funcs, stack)?.num(b.1)?,
        ),
        Expr::Binary(a, BinaryOp::Mul, b) => Value::Num(
            eval_expr(a, funcs, stack)?.num(a.1)? * eval_expr(b, funcs, stack)?.num(b.1)?,
        ),
        Expr::Binary(a, BinaryOp::Div, b) => Value::Num(
            eval_expr(a, funcs, stack)?.num(a.1)? / eval_expr(b, funcs, stack)?.num(b.1)?,
        ),
        Expr::Binary(a, BinaryOp::GreaterThan, b) => {
            Value::Bool(eval_expr(a, funcs, stack)?.num(a.1)? > eval_expr(b, funcs, stack)?.num(b.1)?)
        }
        Expr::Binary(a, BinaryOp::LessThan, b) => {
            Value::Bool(eval_expr(a, funcs, stack)?.num(a.1)? < eval_expr(b, funcs, stack)?.num(b.1)?)
        }
        Expr::Binary(a, BinaryOp::GreaterEq, b) => {
            Value::Bool(eval_expr(a, funcs, stack)?.num(a.1)? >= eval_expr(b, funcs, stack)?.num(b.1)?)
        }
        Expr::Binary(a, BinaryOp::LessEq, b) => {
            Value::Bool(eval_expr(a, funcs, stack)?.num(a.1)? <= eval_expr(b, funcs, stack)?.num(b.1)?)
        }
        Expr::Binary(a, BinaryOp::Eq, b) => {
            Value::Bool(eval_expr(a, funcs, stack)? == eval_expr(b, funcs, stack)?)
        }
        Expr::Binary(a, BinaryOp::NotEq, b) => {
            Value::Bool(eval_expr(a, funcs, stack)? != eval_expr(b, funcs, stack)?)
        }
        Expr::Binary(a, BinaryOp::And, b) => {
            if let Value::Bool(a_b) = eval_expr(a, funcs, stack)? {
                if let Value::Bool(b_b) = eval_expr(b, funcs, stack)? {
                    Value::Bool(a_b && b_b)
                }
                else {
                    return Err(Error {
                        span: b.1,
                        msg: format!("Argument 2 must be of type bool"),
                    });
                }
            }
            else {
                return Err(Error {
                    span: b.1,
                    msg: format!("Argument 1 must be of type bool"),
                });
            }
        }
        Expr::Binary(a, BinaryOp::Or, b) => {
            if let Value::Bool(a_b) = eval_expr(a, funcs, stack)? {
                if let Value::Bool(b_b) = eval_expr(b, funcs, stack)? {
                    Value::Bool(a_b || b_b)
                }
                else {
                    return Err(Error {
                        span: b.1,
                        msg: format!("Argument 2 must be of type bool"),
                    });
                }
            }
            else {
                return Err(Error {
                    span: b.1,
                    msg: format!("Argument 1 must be of type bool"),
                });
            }
            
        }
        Expr::Call(func, args) => {
            let f = eval_expr(func, funcs, stack)?;
            match f {
                Value::Func(name) => {
                    let f = &funcs[&name];
                    let mut stack = if f.args.len() != args.0.len() {
                        return Err(Error {
                            span: expr.1,
                            msg: format!("'{}' called with wrong number of arguments (expected {}, found {})", name, f.args.len(), args.0.len()),
                        });
                    } else {
                        f.args
                            .iter()
                            .zip(args.0.iter())
                            .map(|(name, arg)| Ok((*name, eval_expr(arg, funcs, stack)?)))
                            .collect::<Result<_, _>>()?
                    };
                    eval_expr(&f.body, funcs, &mut stack)?
                }
                f => {
                    return Err(Error {
                        span: func.1,
                        msg: format!("'{:?}' is not callable", f),
                    })
                }
            }
        }

        Expr::If(cond, a, b) => {
            let c = eval_expr(cond, funcs, stack)?;
            match c {
                Value::Bool(true) => eval_expr(a, funcs, stack)?,
                Value::Bool(false) => eval_expr(b, funcs, stack)?,
                c => {
                    return Err(Error {
                        span: cond.1,
                        msg: format!("Conditions must be booleans, found '{:?}'", c),
                    })
                }
            }
        }

        Expr::Fidx(items) => Value::Num({
            if items.len() != 2 {
                return Err(Error {
                    span: items[0].1, 
                    msg: format!("Wrong number of args (expected 2)"),
                });
            } else {
                let arg1 = eval_expr(&items[0], funcs, stack)?;
                let arg2 = eval_expr(&items[1], funcs, stack)?;
                if let Value::List(l) = arg1 {
                    if l.contains(&arg2) {
                        let index = l.iter().position(|r| *r == arg2).unwrap();
                        let val = index as f64;
                        val
                    } else {
                        return Err(Error {
                            span: items[0].1, 
                            msg: format!("Value not found in list"),
                        });
                    }
                } else {
                    return Err(Error {
                        span: items[0].1, 
                        msg: format!("Arg 1 must be a list"),
                    });
                }
            }
        }),

        Expr::SleepStr(a) => {
            let v = eval_expr(a, funcs, stack)?;
            let t = eval_expr(a, funcs, stack)?;
            sleep(Duration::from_millis(t.clone().num(a.1)?.round() as u64));
            v
        },
        Expr::Flush(a) => {
            let val = eval_expr(a, funcs, stack)?;
            clear_screen();
            val    
        },
        Expr::Print(a) => {
            let val = eval_expr(a, funcs, stack)?;
            print!("{}", val);
            val
        },
        Expr::PrintLine(a) => {
            let val = eval_expr(a, funcs, stack)?;
            println!("{}", val);
            val
        },
        Expr::InputBuf(a) => Value::Str({
            let val = eval_expr(a, funcs, stack)?;
            println!("{}", val);
            let mut line = String::new();
            let _b1 = std::io::stdin().read_line(&mut line).unwrap();
            line.leak().trim()
        }),

        Expr::Idx(items) => {
            if items.len() != 2 {
                return Err(Error {
                    span: items[0].1, 
                    msg: format!("Wrong number of args (expected 2)"),
                });
            } else {
                let arg1 = eval_expr(&items[0], funcs, stack)?;
                let arg2 = eval_expr(&items[1], funcs, stack)?;
                if let Value::List(l) = arg1 {
                    if let Value::Num(n) = arg2 {
                        if (n.round() as i64) > ((l.len() - 1) as i64) || (n.round() as i64) < (0) {
                            return Err(Error {
                                span: items[1].1, 
                                msg: format!("Index out of range 0..{}", l.len() - 1),
                            });
                        }
                        else {
                            let val = &l[(n.round() as i64) as usize];
                            val.to_owned()
                        }
                    } else {
                        return Err(Error {
                            span: items[1].1, 
                            msg: format!("Arg 2 must be a num"),
                        });
                    }
                } else {
                    return Err(Error {
                        span: items[0].1, 
                        msg: format!("Arg 1 must be a list"),
                    });
                }
            }
        },

        Expr::RemIdx(items) => Value::List({
            if items.len() != 2 {
                return Err(Error {
                    span: items[0].1, 
                    msg: format!("Wrong number of args (expected 2)"),
                });
            } else {
                let arg1 = eval_expr(&items[0], funcs, stack)?;
                let arg2 = eval_expr(&items[1], funcs, stack)?;
                if let Value::List(mut l) = arg1 {
                    if let Value::Num(n) = arg2 {
                        if (n.round() as i64) > ((l.len() - 1) as i64) || (n.round() as i64) < (0) {
                            return Err(Error {
                                span: items[1].1, 
                                msg: format!("Index out of range 0..{}", l.len() - 1),
                            });
                        }
                        else {
                            l.remove((n.round() as i64) as usize);
                            l.clone()
                        }
                    } else {
                        return Err(Error {
                            span: items[1].1, 
                            msg: format!("Arg 2 must be a num"),
                        });
                    }
                } else {
                    return Err(Error {
                        span: items[0].1, 
                        msg: format!("Arg 1 must be a list"),
                    });
                }
            }
        }),

        Expr::RepIdx(items) => Value::List({
            if items.len() != 3 {
                return Err(Error {
                    span: items[0].1, 
                    msg: format!("Wrong number of args (expected 2)"),
                });
            } else {
                let arg1 = eval_expr(&items[0], funcs, stack)?;
                let arg2 = eval_expr(&items[1], funcs, stack)?;
                let arg3 = eval_expr(&items[2], funcs, stack)?;
                if let Value::List(mut l) = arg1 {
                    if let Value::Num(n) = arg2 {
                        if (n.round() as i64) > ((l.len() - 1) as i64) || (n.round() as i64) < (0) {
                            return Err(Error {
                                span: items[1].1, 
                                msg: format!("Index out of range 0..{}", l.len() - 1),
                            });
                        }
                        else {
                            l[(n.round() as i64) as usize] = arg3.clone();
                            l.clone()
                        }
                    } else {
                        return Err(Error {
                            span: items[1].1, 
                            msg: format!("Arg 2 must be a num"),
                        });
                    }
                } else {
                    return Err(Error {
                        span: items[0].1, 
                        msg: format!("Arg 1 must be a list"),
                    });
                }
            }
        }),

        Expr::Rng(items) => Value::Num({
            if items.len() != 2 {
                return Err(Error {
                    span: items[0].1, 
                    msg: format!("Wrong number of args (expected 2)"),
            })
            } else {
                let arg1 = eval_expr(&items[0], funcs, stack)?;
                let arg2 = eval_expr(&items[1], funcs, stack)?;
                if let Value::Num(x) = arg1 {
                    if let Value::Num(y) = arg2 {
                        let x_x = (x.clone().round() as f64) as i64;
                        let y_y = ((y.clone().round() as f64) as i64) + 1;
                        let num = (rand::thread_rng().gen_range(x_x..y_y)) as f64;
                        num
                    } else {
                        return Err(Error {
                            span: items[1].1.clone(),
                            msg: format!("Value must be numeric"),
                        });
                    }
                } else {
                    return Err(Error {
                        span: items[0].1.clone(),
                        msg: format!("Value must be numeric"),
                    });
                }
            }
        }),

        Expr::Round(f) => Value::Num({
            let f_expr = eval_expr(f, funcs, stack)?;
            if let Value::Num(n) = f_expr {
                n.clone().round() as f64
            } else {
                return Err(Error {
                    span: f.1.clone(),
                    msg: format!("Value must be numeric"),
                });
            }
        }),

        Expr::DefStr(a) => Value::Str({
            let val = eval_expr(a, funcs, stack)?.to_string();
            val.leak()
        }),

        Expr::DefNum(a) => Value::Num({
            let c = eval_expr(a, funcs, stack)?;
            if let Value::Num(s) = c {
                s
            } else if let Value::Str(s) = c {
                if s.to_string().parse::<f64>().is_ok() {
                    let f: f64 = s.parse().unwrap();
                    f
                }
                else {
                    return Err(Error {
                        span: a.1.clone(),
                        msg: format!("Value must be numeric"),
                    });
                }
            }
            else {
                return Err(Error {
                    span: a.1.clone(),
                    msg: format!("Value must be numeric"),
                });
            }
        }),

        Expr::Len(a) => Value::Num({
            let c = eval_expr(a, funcs, stack)?;
            if let Value::Num(_n) = c {
                return Err(Error {
                    span: a.1.clone(),
                    msg: format!("Cannot find len() of numeric"),
                });
            } else if let Value::Str(s) = c {
                s.to_string().len() as f64
            } else if let Value::List(s) = c {
                s.len() as f64
            }
            else {
                return Err(Error {
                    span: a.1.clone(),
                    msg: format!("Invalid value in len()"),
                });
            }
        }),

        Expr::Break =>  {
            return Ok(Value::Break);
        }

        Expr::WhileLoop(cond, body) => {
            loop {
                let condition_val = eval_expr(cond, funcs, stack)?;
                //println!("{:?}", condition_val);
                if let Value::Bool(true) = condition_val {
                    if let Value::Break = eval_expr(body, funcs, stack)? {
                        return Ok(Value::Break);
                    }
                } else if let Value::Bool(false) = condition_val {
                    break;
                } else {
                    return Err(Error {
                        span: cond.1.clone(),
                        msg: format!("Conditions must be booleans, found '{:?}'", condition_val),
                    });
                }
            }
            return Ok(Value::Bool(true));
        }


        Expr::ForLoop(var, iterable, body) => {
            let iterable_val = eval_expr(iterable, funcs, stack)?;
            if let Value::Str(s) = iterable_val {
                for item in s.chars() {
                    stack.push((var, Value::Str(&char_to_str_converter(item))));
                    if let Value::Break = eval_expr(body, funcs, stack)? {
                        stack.pop();
                        return Ok(Value::Break);
                    }
                    stack.pop();
                }
                Value::Str(s)
            } else if let Value::Num(n) = iterable_val {
                let n_int = n.round() as i64;
                for i in 0..n_int {
                    stack.push((var, Value::Num(i as f64)));
                    if let Value::Break = eval_expr(body, funcs, stack)? {
                        stack.pop();
                        return Ok(Value::Break);
                    }
                    stack.pop();
                }
                Value::Num(n)
            }   else if let Value::List(n) = iterable_val {
                    for item in n.clone() {
                        stack.push((var, Value::Str(&string_to_str_converter(item.to_string()))));
                        if let Value::Break = eval_expr(body, funcs, stack)? {
                            stack.pop();
                            return Ok(Value::Break);
                        }
                        stack.pop();
                    }
                Value::List(n)
            } else {
                return Err(Error {
                    span: iterable.1.clone(),
                    msg: format!("Expected a string or number in 'for' loop, found '{:?}'", iterable_val),
                });
            }
        }
    })
}

// This gets called by main.rs
pub fn do_lang() {
    let filename = env::args().nth(1).expect("Expected file argument");

    let src = fs::read_to_string(&filename).expect("Failed to read file");

    
    let (tokens, mut errs) = lexer().parse(src.as_str()).into_output_errors();
    
    // Optionally enable if you want to see the tokens in your script
    // For debugging

    //println!("{:?}", tokens);
    
    let parse_errs = if let Some(tokens) = &tokens {
        let (ast, parse_errs) = funcs_parser()
            .map_with(|ast, e| (ast, e.span()))
            .parse(tokens.as_slice().spanned((src.len()..src.len()).into()))
            .into_output_errors();

        if let Some((funcs, file_span)) = ast.filter(|_| errs.len() + parse_errs.len() == 0) {
            if let Some(main) = funcs.get("main") {
                if !main.args.is_empty() {
                    errs.push(Rich::custom(
                        main.span,
                        "The main function cannot have arguments".to_string(),
                    ))
                } else {
                    match eval_expr(&main.body, &funcs, &mut Vec::new()) {
                        Ok(_val) => println!(""),
                        Err(e) => errs.push(Rich::custom(e.span, e.msg)),
                    }
                }
            } else {
                errs.push(Rich::custom(
                    file_span,
                    "Programs need a main function but none was found".to_string(),
                ));
            }
        }

        parse_errs
    } else {
        Vec::new()
    };

    errs.into_iter()
        .map(|e| e.map_token(|c| c.to_string()))
        .chain(
            parse_errs
                .into_iter()
                .map(|e| e.map_token(|tok| tok.to_string())),
        )
        .for_each(|e| {
            Report::build(ReportKind::Error, filename.clone(), e.span().start)
                .with_message(e.to_string())
                .with_config(Config::default().with_color(true))
                .with_label(
                    Label::new((filename.clone(), e.span().into_range()))
                        .with_message(e.reason().to_string())
                )
                .with_labels(e.contexts().map(|(label, span)| {
                    Label::new((filename.clone(), span.into_range()))
                        .with_message(format!("while parsing this {}", label))
                }))
                .finish()
                .print(sources([(filename.clone(), src.clone())]))
                .unwrap()
        });
}
