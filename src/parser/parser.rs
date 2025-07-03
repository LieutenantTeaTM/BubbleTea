use std::{collections::HashMap, iter::Peekable, slice::Iter, vec};

use crate::{
    general::ast::{Expr, ExternFunction, IterTarget, RangeIter, Type, Value},
    lexer::lexer::{Lexer, Token, combine_tokens},
    utils::utils::Utililites,
};

pub struct Parser {
    rpn_output: Vec<Token>,
    is_cast: bool,
    pub ast_expr: Expr,
    pub functions: HashMap<String, Function>,
    pub variable_stack: HashMap<String, Expr>,
    pub variable_types: HashMap<String, Type>,
    pub utils: Utililites,
    pub extern_funcs: Vec<ExternFunction>,
}

#[derive(Clone)]
pub struct Function {
    pub params: Vec<(bool, String, Type)>,
    pub body: Vec<Expr>,
    pub return_type: Type,
}

impl Parser {
    pub fn new() -> Self {
        Parser {
            is_cast: false,
            rpn_output: Vec::new(),
            ast_expr: Expr::Value {
                value: Value::Null,
                is_negate_not: false,
                is_negate_minus: false,
            },
            extern_funcs: Vec::new(),
            variable_stack: HashMap::new(),
            variable_types: HashMap::new(),
            functions: HashMap::new(),
            utils: Utililites::new(),
        }
    }

    fn precedence(&self, op: &str) -> usize {
        match op {
            "||" => 1,
            "&&" => 2,
            "::" | "!:" => 3,
            ">" | "<" | ">:" | "<:" => 4,
            "+" | "-" => 5,
            "*" | "/" => 6,
            "!" => 7,
            _ => 0,
        }
    }

    pub fn pre_parse_while(&mut self, iter: &mut Peekable<Iter<Token>>) -> Expr {
        let mut new_tokens = vec![Token::While];

        let mut inner_depth = 0;
        let mut started = false;

        while let Some(token) = iter.peek().copied() {
            if !(token == &Token::LCurly) {
                new_tokens.push(iter.next().unwrap().clone());
            } else {
                iter.next();
            }

            match token {
                Token::LCurly => {
                    inner_depth += 1;
                    started = true;
                    new_tokens.push(token.clone());
                }
                #[allow(unused_assignments)]
                Token::RCurly => {
                    inner_depth -= 1;
                    if inner_depth == 0 && started {
                        break;
                    }
                }
                _ => {}
            }
        }

        let temp_lexer = Lexer {
            tokens: new_tokens.clone(),
        };

        self.parse_expression(&temp_lexer)
    }

    pub fn pre_parse_for(&mut self, iter: &mut Peekable<Iter<Token>>) -> Expr {
        let mut new_tokens = vec![Token::For];

        let mut inner_depth = 0;
        let mut started = false;

        while let Some(token) = iter.peek().copied() {
            if !(token == &Token::LCurly) {
                new_tokens.push(iter.next().unwrap().clone());
            } else {
                iter.next();
            }

            match token {
                Token::LCurly => {
                    inner_depth += 1;
                    started = true;
                    new_tokens.push(token.clone());
                }
                #[allow(unused_assignments)]
                Token::RCurly => {
                    inner_depth -= 1;
                    if inner_depth == 0 && started {
                        break;
                    }
                }
                _ => {}
            }
        }

        let temp_lexer = Lexer {
            tokens: new_tokens.clone(),
        };

        self.parse_expression(&temp_lexer)
    }

    pub fn pre_parse_if(&mut self, iter: &mut Peekable<Iter<Token>>) -> Expr {
        let mut new_tokens = vec![Token::If];

        let mut inner_depth = 0;
        let mut started = false;

        let mut in_else_block = false;
        while let Some(token) = iter.peek().copied() {
            if !(token == &Token::LCurly && in_else_block) {
                new_tokens.push(iter.next().unwrap().clone());
            } else {
                iter.next();
            }

            match token {
                Token::LCurly => {
                    inner_depth += 1;
                    started = true;
                }
                #[allow(unused_assignments)]
                Token::RCurly => {
                    inner_depth -= 1;
                    if inner_depth == 0 && started {
                        match iter.peek() {
                            Some(Token::Elif) => {
                                // Continue looping to capture this next branch
                            }
                            Some(Token::Else) => {
                                in_else_block = true;
                            }
                            _ => break,
                        }
                    }
                }
                _ => {}
            }
        }

        let temp_lexer = Lexer {
            tokens: new_tokens.clone(),
        };

        self.parse_expression(&temp_lexer)
    }

    pub fn parse_function_definition_body(
        &mut self,
        iter: &mut Peekable<Iter<Token>>,
        body: &mut Vec<Expr>,
        expr_tokens: &mut Vec<Token>,
        brace_depth: &mut i32,
    ) {
        while let Some(token2) = iter.peek() {
            if **token2 == Token::RCurly && *brace_depth == 0 {
                iter.next(); // consume `}`
                break;
            }

            #[allow(unused_assignments)]
            let mut token = None;
            let iter_token = iter.next().unwrap().clone();
            token = Some(iter_token);

            match token.clone().unwrap() {
                Token::LCurly => {
                    *brace_depth += 1;

                    expr_tokens.push(token.unwrap().clone());
                }
                Token::RCurly => {
                    *brace_depth -= 1;

                    expr_tokens.push(token.unwrap().clone());

                    if *brace_depth == 0 {
                        let temp_lexer = Lexer {
                            tokens: expr_tokens.clone(),
                        };

                        if !expr_tokens.is_empty() {
                            let e = self.parse_expression(&temp_lexer);
                            body.push(e);
                        }

                        expr_tokens.clear();
                    }
                }

                Token::While => {
                    let b = self.pre_parse_while(iter);
                    body.push(b);
                }

                Token::For => {
                    let b = self.pre_parse_for(iter);
                    body.push(b);
                }

                Token::If => {
                    let b = self.pre_parse_if(iter);
                    body.push(b);
                }
                Token::Semicolon if *brace_depth == 0 => {
                    expr_tokens.push(token.unwrap().clone());
                    let temp_lexer = Lexer {
                        tokens: expr_tokens.clone(),
                    };
                    let e = self.parse_expression(&temp_lexer);
                    body.push(e);
                    expr_tokens.clear();
                }
                _ => {
                    expr_tokens.push(token.unwrap().clone());
                }
            }
        }
    }

    pub fn parse_function_definition(&mut self, tokens: &[Token]) -> Expr {
        self.variable_stack.clear();
        self.variable_types.clear();
        let mut iter = tokens.iter().peekable();
        assert_eq!(iter.next(), Some(&Token::Fn));

        let (name, params) = match iter.next() {
            Some(Token::FunctionCall(name, arg_tokens)) => {
                let mut params = Vec::new();
                let mut param_iter = arg_tokens.iter().peekable();

                let mut mutable = false;
                let mut is_pass_by_ref = false;
                while let Some(token) = param_iter.next() {
                    match token {
                        Token::Mut => {
                            if is_pass_by_ref {
                                panic!("Function arg is pass by reference, cannot cast to mutable")
                            }
                            mutable = true;
                        }
                        Token::Ref => {
                            if mutable {
                                panic!("Function arg is pass by value, cannot cast to mutable")
                            }
                            is_pass_by_ref = true;
                        }
                        Token::Ident(param_name) => {
                            assert_eq!(param_iter.next(), Some(&Token::Colon));
                            let ty = match param_iter.next() {
                                Some(Token::Type(t)) => self.type_str_to_enum(t.clone()),
                                _ => panic!("Expected type"),
                            };
                            params.push((mutable, param_name.clone(), ty.clone()));

                            if let Some(Token::Comma) = param_iter.peek() {
                                param_iter.next(); // consume comma
                                mutable = false;
                            }

                            let ts = self.type_enum_to_str(ty.clone());
                            let t = match ty.clone() {
                                Type::Int => Value::Int(0),
                                Type::Float => Value::Float(0.0),
                                Type::Bool => Value::Bool(false),
                                Type::Str => Value::Str("".to_string()),
                                Type::Null => Value::Null,
                            };

                            let e = Expr::VarDecl {
                                name: param_name.to_owned(),
                                mutable,
                                type_name: ts,
                                value: Box::new(Expr::Value {
                                    value: t,
                                    is_negate_not: false,
                                    is_negate_minus: false,
                                }),
                            };

                            self.variable_stack.insert(param_name.to_string(), e);
                            self.variable_types.insert(param_name.to_owned(), ty);
                        }
                        _ => panic!("Unexpected token in function param list: {:?}", token),
                    }
                }

                (name.clone(), params)
            }
            _ => panic!("Expected function name as function call"),
        };

        assert_eq!(iter.next(), Some(&Token::InputOp));
        let mut return_type = Type::Null;
        if let Token::Type(t) = iter.next().unwrap() {
            return_type = self.type_str_to_enum(t.to_string());
        }

        assert_eq!(iter.next(), Some(&Token::LCurly)); // consume `{`

        let mut body: Vec<Expr> = Vec::new();
        let mut expr_tokens: Vec<Token> = Vec::new();
        let mut brace_depth = 0;

        self.parse_function_definition_body(
            &mut iter,
            &mut body,
            &mut expr_tokens,
            &mut brace_depth,
        );

        self.functions.insert(
            name.clone(),
            Function {
                params: params.clone(),
                body: body.clone(),
                return_type: return_type.clone(),
            },
        );

        Expr::FunctionDef {
            name,
            params,
            body: Box::new(body),
            return_type,
        }
    }

    pub fn parse_return(&mut self, tokens: &[Token]) -> Expr {
        let mut iter = tokens.iter().peekable();

        assert_eq!(iter.next(), Some(&Token::OutputOp));

        if *iter.clone().last().unwrap() != Token::Semicolon {
            panic!("Expected ';' at end of line")
        }

        // Grab everything after the `<-` for expression
        let mut expr_tokens: Vec<Token> = iter.cloned().collect();
        expr_tokens.remove(expr_tokens.len() - 1);
        let combined = combine_tokens(expr_tokens.iter().peekable());
        let mut temp_lexer = Lexer::new();
        temp_lexer.tokenize(&combined);

        self.to_rpn(temp_lexer.clone());
        self.build_ast();

        Expr::Return(Box::new(self.ast_expr.clone()))
    }

    #[allow(clippy::collapsible_if)]
    pub fn parse_function_call(
        &mut self,
        tokens: &[Token],
        is_negate_not: bool,
        is_negate_minus: bool,
    ) -> Expr {
        let mut iter = tokens.iter().peekable();

        if *iter.clone().last().unwrap() != Token::Semicolon {
            panic!("Expected ';' at end of line")
        }

        if iter.clone().last() == Some(&Token::Semicolon) {
            let (name, args) = match iter.next() {
                Some(Token::FunctionCall(name, args_tokens)) => {
                    let mut args = Vec::new();
                    let mut current_arg = Vec::new();
                    let mut paren_depth = 1;

                    for token in args_tokens {
                        match token {
                            Token::Comma if paren_depth == 1 => {
                                let temp_lexer = Lexer {
                                    tokens: current_arg.clone(),
                                };
                                self.to_rpn(temp_lexer.clone());
                                self.build_ast();
                                args.push(self.ast_expr.clone());
                                current_arg.clear();
                            }
                            Token::LParen => {
                                paren_depth += 1;
                                current_arg.push(token.clone());
                            }
                            Token::RParen => {
                                paren_depth -= 1;
                                if paren_depth == 0 {
                                    break;
                                } else {
                                    current_arg.push(token.clone());
                                }
                            }
                            Token::Semicolon => {}
                            _ => current_arg.push(token.clone()),
                        }
                    }

                    if !current_arg.is_empty() {
                        let temp_lexer = Lexer {
                            tokens: current_arg,
                        };
                        self.to_rpn(temp_lexer.clone());
                        self.build_ast();
                        args.push(self.ast_expr.clone());
                    }

                    (name.clone(), args)
                }
                _ => panic!("Expected function name as function call"),
            };

            Expr::FunctionCall {
                name,
                args,
                is_negate_minus,
                is_negate_not,
            }
        } else {
            let (name, args) = match iter.next() {
                Some(Token::FunctionCall(name, _)) => {
                    let mut args = Vec::new();
                    let mut current_arg = Vec::new();
                    let mut paren_depth = 1;

                    for token in iter {
                        match token {
                            Token::Comma if paren_depth == 1 => {
                                let temp_lexer = Lexer {
                                    tokens: current_arg.clone(),
                                };
                                self.to_rpn(temp_lexer.clone());
                                self.build_ast();
                                args.push(self.ast_expr.clone());
                                current_arg.clear();
                            }
                            Token::LParen => {
                                paren_depth += 1;
                                current_arg.push(token.clone());
                            }
                            Token::RParen => {
                                paren_depth -= 1;
                                if paren_depth == 0 {
                                    break;
                                } else {
                                    current_arg.push(token.clone());
                                }
                            }
                            Token::Semicolon => {}
                            _ => current_arg.push(token.clone()),
                        }
                    }

                    if !current_arg.is_empty() {
                        let temp_lexer = Lexer {
                            tokens: current_arg,
                        };
                        self.to_rpn(temp_lexer.clone());
                        self.build_ast();
                        args.push(self.ast_expr.clone());
                    }

                    (name.clone(), args)
                }
                _ => panic!("Expected function name as function call"),
            };

            Expr::FunctionCall {
                name,
                args,
                is_negate_minus,
                is_negate_not,
            }
        }
    }

    #[allow(clippy::wrong_self_convention)]
    // Shunting Yard Algorithm
    pub fn to_rpn(&mut self, lexer: Lexer) {
        let mut output = Vec::new();

        let mut ops = Vec::new();

        for token in lexer.tokens {
            match token {
                Token::Number(_) => output.push(token),
                Token::Float(_) => output.push(token),
                /*Token::Op(c1) => {
                    while let Some(Token::Op(c2)) = ops.last() {
                        if self.precedence(c2) >= self.precedence(&c1) {
                            output.push(ops.pop().unwrap());
                        } else {
                            break;
                        }
                    }
                    ops.push(Token::Op(c1));
                }*/
                Token::Op(c1) => {
                    while let Some(top) = ops.last() {
                        match top {
                            Token::Op(c2) => {
                                if self.precedence(c2) >= self.precedence(&c1) {
                                    output.push(ops.pop().unwrap());
                                } else {
                                    break;
                                }
                            }
                            Token::LParen => {
                                break; // <- THIS IS MISSING in your implementation
                            }
                            _ => {
                                break;
                            }
                        }
                    }
                    ops.push(Token::Op(c1));
                }
                Token::UnaryMinus => {
                    ops.push(token);
                }
                Token::InputMacro => {
                    ops.push(token);
                }
                Token::Cast(_, _) => {
                    //self.is_cast = true;
                    output.push(token);
                }
                Token::FunctionCall(_, _) => output.push(token),
                Token::CustomMacroCall(_, _) => output.push(token),
                Token::Ident(var) => {
                    output.push(Token::Ident(var));
                }
                Token::LParen => {
                    if self.is_cast {
                        //output.push(Token::LParen);
                    } else {
                        ops.push(Token::LParen)
                    }
                }
                Token::RParen => {
                    if self.is_cast {
                        self.is_cast = false;
                        //output.push(Token::RParen);
                    } else {
                        while let Some(top) = ops.pop() {
                            if let Token::LParen = top {
                                break;
                            } else {
                                output.push(top);
                            }
                        }
                    }
                }
                Token::Str(_) => {
                    output.push(token);
                }
                Token::Bool(_) => {
                    output.push(token);
                }
                _ => {}
            }
        }

        while let Some(op) = ops.pop() {
            output.push(op);
        }

        self.rpn_output = output;
    }

    pub fn build_ast(&mut self) {
        let mut stack: Vec<Expr> = Vec::new();

        let rpn = self.rpn_output.clone();
        let mut i = 0;

        while i < rpn.len() {
            match &rpn[i] {
                Token::Number(n) => {
                    i += 1;
                    stack.push(Expr::Value {
                        value: Value::Int(*n),
                        is_negate_not: false,
                        is_negate_minus: false,
                    });
                }
                Token::Float(f) => {
                    i += 1;
                    stack.push(Expr::Value {
                        value: Value::Float(*f),
                        is_negate_not: false,
                        is_negate_minus: false,
                    });
                }
                Token::InputMacro => {
                    i += 1;
                    stack.push(self.parse_input_macro(&rpn, false));
                }
                Token::Str(s) => {
                    i += 1;
                    let mut value_owned = s.to_string();
                    for _ in value_owned.clone().chars() {
                        value_owned = value_owned.replace("\\n", "\n");
                        // For silly ANSI colors (may not be enabled on Windows by default) just for fun!
                        value_owned = value_owned.replace("\\x1b", "\x1b");
                        value_owned = value_owned.replace("\\t", "\t");
                        value_owned = value_owned.replace("\\r", "\r");
                        value_owned = value_owned.replace("\\\"", "\"");
                        value_owned = value_owned.replace("\\\\", "\\");
                    }
                    stack.push(Expr::Value {
                        value: Value::Str(value_owned.clone()),
                        is_negate_not: false,
                        is_negate_minus: false,
                    })
                }
                Token::Bool(b) => {
                    i += 1;
                    stack.push(Expr::Value {
                        value: Value::Bool(*b),
                        is_negate_not: false,
                        is_negate_minus: false,
                    })
                }
                Token::Cast(v, t) => {
                    i += 1;

                    stack.push(Expr::Cast {
                        expr: Box::new(self.parse_cast_value(v)),
                        target_type: self.parse_cast_type(t),
                    });
                }
                Token::FunctionCall(name, token_body) => {
                    if !token_body.is_empty() {
                        if token_body[0] == Token::Fn {
                            stack.push(self.parse_function_definition(token_body));
                            i += 1;
                        } else {
                            stack.push(Expr::FunctionCall {
                                name: name.to_string(),
                                args: self.parse_function_arguments(token_body, false),
                                is_negate_minus: false,
                                is_negate_not: false,
                            });
                            i += 1;
                        }
                    } else {
                        stack.push(Expr::FunctionCall {
                            name: name.to_string(),
                            args: self.parse_function_arguments(token_body, false),
                            is_negate_minus: false,
                            is_negate_not: false,
                        });
                        i += 1;
                    }
                }
                Token::CustomMacroCall(name, body) => {
                    stack.push(Expr::CustomMacro {
                        name: name.to_string(),
                        args: self.parse_function_arguments(body, false),
                    });
                    i += 1;
                }
                #[allow(clippy::collapsible_if)]
                Token::Ident(var) => {
                    let mut matched = false;
                    if i > 1 {
                        let output = self.rpn_output.clone();
                        if output.clone().get(i - 1).is_some() {
                            let before = output.get(i - 1).unwrap();
                            if *before == Token::Op("!".to_owned()) {
                                matched = true;
                            }
                        }
                    }

                    if !matched {
                        stack.push(Expr::Ident(var.clone(), false, false));
                        i += 1;
                    }
                }
                Token::Op(op) if op == "!" => {
                    let val = stack.pop().unwrap();
                    match val {
                        Expr::Value { value, .. } => {
                            stack.push(Expr::Value {
                                value,
                                is_negate_not: true,
                                is_negate_minus: false,
                            });
                            i += 1;
                        }
                        Expr::Ident(v, _, _) => {
                            stack.push(Expr::Ident(v.clone(), true, false));
                            i += 1;
                        }
                        Expr::FunctionCall {
                            name,
                            args: _,
                            is_negate_minus: _,
                            is_negate_not: _,
                        } => {
                            if let Token::FunctionCall(_, args2) = &rpn[i - 1] {
                                let mut args = Vec::new();
                                let mut current_arg = Vec::new();
                                let mut paren_depth = 1;
                                for token in args2 {
                                    match token {
                                        Token::Comma if paren_depth == 1 => {
                                            let temp_lexer = Lexer {
                                                tokens: current_arg.clone(),
                                            };
                                            self.to_rpn(temp_lexer.clone());
                                            self.build_ast();
                                            args.push(self.ast_expr.clone());
                                            current_arg.clear();
                                        }
                                        Token::LParen => {
                                            paren_depth += 1;
                                            current_arg.push(token.clone());
                                        }
                                        Token::RParen => {
                                            paren_depth -= 1;
                                            if paren_depth == 0 {
                                                break;
                                            } else {
                                                current_arg.push(token.clone());
                                            }
                                        }
                                        _ => current_arg.push(token.clone()),
                                    }
                                }

                                if !current_arg.is_empty() {
                                    let temp_lexer = Lexer {
                                        tokens: current_arg.clone(),
                                    };
                                    self.to_rpn(temp_lexer.clone());
                                    self.build_ast();
                                    args.push(self.ast_expr.clone());
                                }

                                stack.push(Expr::FunctionCall {
                                    name,
                                    args,
                                    is_negate_not: true,
                                    is_negate_minus: false,
                                });
                                i += 1;
                            }
                        }
                        Expr::BinaryOp { .. } => {
                            i += 1;
                            stack.push(Expr::Value {
                                value: Value::Bool(false),
                                is_negate_not: true,
                                is_negate_minus: false,
                            });
                        }
                        _ => panic!("Unary '!' can only be applied to bools"),
                    }
                }
                Token::Op(op) => {
                    let right = Box::new(stack.pop().expect("Missing right operand"));
                    let left = Box::new(stack.pop().expect("Missing left operand"));
                    i += 1;
                    stack.push(Expr::BinaryOp {
                        op: op.clone(),
                        left,
                        right,
                    });
                }
                Token::UnaryMinus => {
                    let val = stack.pop().unwrap();
                    match val {
                        Expr::Value { value, .. } => {
                            match value {
                                Value::Int(i2) => {
                                    stack.push(Expr::Value {
                                        value: Value::Int(i2),
                                        is_negate_not: false,
                                        is_negate_minus: true,
                                    });
                                }
                                Value::Float(f2) => {
                                    stack.push(Expr::Value {
                                        value: Value::Float(f2),
                                        is_negate_not: false,
                                        is_negate_minus: true,
                                    });
                                }
                                _ => {}
                            }

                            i += 1;
                        }
                        Expr::Ident(v, _, _) => {
                            stack.push(Expr::Ident(v.clone(), false, true));
                            i += 1;
                        }
                        Expr::FunctionCall {
                            name,
                            args: _,
                            is_negate_minus: _,
                            is_negate_not: _,
                        } => {
                            if let Token::FunctionCall(_, args2) = &rpn[i - 1] {
                                let mut args = Vec::new();
                                let mut current_arg = Vec::new();
                                let mut paren_depth = 1;
                                for token in args2 {
                                    match token {
                                        Token::Comma if paren_depth == 1 => {
                                            let temp_lexer = Lexer {
                                                tokens: current_arg.clone(),
                                            };
                                            self.to_rpn(temp_lexer.clone());
                                            self.build_ast();
                                            args.push(self.ast_expr.clone());
                                            current_arg.clear();
                                        }
                                        Token::LParen => {
                                            paren_depth += 1;
                                            current_arg.push(token.clone());
                                        }
                                        Token::RParen => {
                                            paren_depth -= 1;
                                            if paren_depth == 0 {
                                                break;
                                            } else {
                                                current_arg.push(token.clone());
                                            }
                                        }
                                        _ => current_arg.push(token.clone()),
                                    }
                                }

                                if !current_arg.is_empty() {
                                    let temp_lexer = Lexer {
                                        tokens: current_arg.clone(),
                                    };
                                    self.to_rpn(temp_lexer.clone());
                                    self.build_ast();
                                    args.push(self.ast_expr.clone());
                                }

                                stack.push(Expr::FunctionCall {
                                    name,
                                    args,
                                    is_negate_not: false,
                                    is_negate_minus: true,
                                });
                                i += 1;
                            }
                        }
                        Expr::BinaryOp { .. } => stack.push(Expr::Value {
                            value: Value::Bool(false),
                            is_negate_not: false,
                            is_negate_minus: false,
                        }),
                        _ => {}
                    }
                }
                _ => {
                    panic!("Unexpected token in RPN for AST: {:?}", rpn[i])
                }
            }
        }

        assert!(stack.len() == 1, "Invalid AST stack");
        self.ast_expr = stack.pop().unwrap();
    }

    fn parse_function_arguments(
        &mut self,
        token_body: &[Token],
        is_function_def: bool,
    ) -> Vec<Expr> {
        let mut args = Vec::new();
        let mut temp_tokens = Vec::new();

        let mut tokens = &token_body[0..];
        if is_function_def {
            tokens = &token_body[1..];
        }

        for token in tokens {
            match token {
                Token::Comma => {
                    if !temp_tokens.is_empty() {
                        let lexer = Lexer {
                            tokens: temp_tokens.clone(),
                        };

                        if temp_tokens.len() > 1 {
                            self.to_rpn(lexer.clone());
                            self.build_ast();

                            args.push(self.ast_expr.clone());
                        } else if let Token::Ident(name) = &temp_tokens[0] {
                            args.push(Expr::Ident(name.to_string(), false, false));
                        } else {
                            args.push(self.parse_expression(&lexer));
                        }

                        temp_tokens.clear();
                    }
                }
                _ => {
                    temp_tokens.push(token.clone());
                }
            }
        }

        if !temp_tokens.is_empty() {
            let lexer = Lexer {
                tokens: temp_tokens.clone(),
            };

            if temp_tokens.len() > 1 {
                self.to_rpn(lexer.clone());
                self.build_ast();
                args.push(self.ast_expr.clone());
            } else if let Token::Ident(name) = &temp_tokens[0] {
                args.push(Expr::Ident(name.to_string(), false, false));
            } else {
                args.push(self.parse_expression(&lexer));
            }
        }

        args
    }

    #[allow(unused_assignments)]
    pub fn parse_var_update(&mut self, tokens: &[Token]) -> Expr {
        let mut iter = tokens.iter().peekable();
        if let Some(Token::Ident(var)) = iter.next() {
            if let Some(Token::Colon) = iter.next() {
                let mut expr_tokens: Vec<Token> = iter.clone().cloned().collect();
                expr_tokens.pop(); // Removes the Semicolon
                let combined = combine_tokens(expr_tokens.iter().peekable());

                let mut temp_lexer = Lexer::new();
                temp_lexer.tokenize(&combined);

                self.to_rpn(temp_lexer.clone());
                self.build_ast();

                if *iter.clone().last().unwrap() != Token::Semicolon {
                    panic!("Expected ';' at end of line")
                }

                {
                    Expr::VarUpdate {
                        var: var.to_string(),
                        new_value: Box::new(self.ast_expr.clone()),
                    }
                }
            } else {
                panic!("Expected ':'")
            }
        } else {
            Expr::Value {
                value: Value::Null,
                is_negate_not: false,
                is_negate_minus: false,
            }
        }
    }

    fn parse_condition(&mut self, iter: &mut Peekable<Iter<Token>>) -> Expr {
        let mut cond_tokens = Vec::new();

        // Skip the "if"
        for token in iter.by_ref() {
            match token {
                Token::If => continue,
                Token::LCurly => break,
                _ => cond_tokens.push(token.clone()),
            }
        }

        let temp_lexer = Lexer {
            tokens: cond_tokens,
        };

        self.to_rpn(temp_lexer);
        self.build_ast();
        self.ast_expr.clone()
    }

    fn parse_condition_while(&mut self, iter: &mut Peekable<Iter<Token>>) -> Expr {
        let mut cond_tokens = Vec::new();

        // Skip the "while"
        for token in iter.by_ref() {
            match token {
                Token::While => continue,
                Token::LCurly => break,
                _ => cond_tokens.push(token.clone()),
            }
        }

        let temp_lexer = Lexer {
            tokens: cond_tokens,
        };

        self.to_rpn(temp_lexer);
        self.build_ast();
        self.ast_expr.clone()
    }

    fn parse_condition_for_init(&mut self, iter: &mut Peekable<Iter<Token>>) -> String {
        let mut cond_tokens = Vec::new();

        for token in iter.by_ref() {
            match token {
                Token::For => continue,
                Token::In => break,
                _ => cond_tokens.push(token.clone()),
            }
        }

        cond_tokens.first().unwrap().to_string()
    }

    /*fn parse_condition_for_after(&mut self, iter: &mut Peekable<Iter<Token>>) -> Expr {
        let mut cond_tokens = Vec::new();

        for token in iter.by_ref() {
            match token {
                Token::In => continue,
                Token::LCurly => break,
                _ => cond_tokens.push(token.clone()),
            }
        }

        let temp_lexer = Lexer {
            tokens: cond_tokens,
        };

        self.to_rpn(temp_lexer);
        self.build_ast();
        self.ast_expr.clone()
    }*/

    fn parse_condition_for_after(&mut self, iter: &mut Peekable<Iter<Token>>) -> IterTarget {
        let mut cond_tokens = Vec::new();

        for token in iter.by_ref() {
            match token {
                Token::In => continue,
                Token::LCurly => break,
                _ => cond_tokens.push(token.clone()),
            }
        }

        let mut sub_iter = cond_tokens.iter().peekable();

        match sub_iter.peek() {
            Some(Token::Number(_)) => {
                // Numeric range case
                let start = Box::new(self.parse_single_expr(&mut sub_iter));

                match sub_iter.next() {
                    Some(Token::Range) => {}
                    other => panic!("Expected '..' in range, found {:?}", other),
                }

                let end = Box::new(self.parse_single_expr(&mut sub_iter));

                let step = if let Some(Token::By) = sub_iter.peek() {
                    sub_iter.next(); // Consume 'by'
                    Some(Box::new(self.parse_single_expr(&mut sub_iter)))
                } else {
                    None
                };

                IterTarget::Range(RangeIter { start, end, step })
            }
            Some(Token::Ident(name)) => {
                let v_type = self.variable_types.get(name).unwrap();
                if v_type == &Type::Int {
                    // Numeric range case
                    let start = Box::new(self.parse_single_expr(&mut sub_iter));

                    match sub_iter.next() {
                        Some(Token::Range) => {}
                        other => panic!("Expected '..' in range, found {:?}", other),
                    }

                    let end = Box::new(self.parse_single_expr(&mut sub_iter));

                    let step = if let Some(Token::By) = sub_iter.peek() {
                        sub_iter.next(); // Consume 'by'
                        Some(Box::new(self.parse_single_expr(&mut sub_iter)))
                    } else {
                        None
                    };

                    IterTarget::Range(RangeIter { start, end, step })
                } else {
                    // Non-range iter expression (string, array, etc)
                    let expr = {
                        let temp_lexer = Lexer {
                            tokens: cond_tokens.clone(),
                        };
                        self.to_rpn(temp_lexer);
                        self.build_ast();
                        Box::new(self.ast_expr.clone())
                    };

                    IterTarget::Expr(expr)
                }
            }
            _ => {
                // Non-range iter expression (string, array, etc)
                let expr = {
                    let temp_lexer = Lexer {
                        tokens: cond_tokens.clone(),
                    };
                    self.to_rpn(temp_lexer);
                    self.build_ast();
                    Box::new(self.ast_expr.clone())
                };

                IterTarget::Expr(expr)
            }
        }
    }

    fn parse_single_expr(&mut self, iter: &mut Peekable<Iter<Token>>) -> Expr {
        let mut expr_tokens = Vec::new();

        while let Some(token) = iter.peek() {
            match token {
                Token::Range | Token::By | Token::LCurly => break,
                _ => expr_tokens.push((token.to_owned()).clone()),
            }
            iter.next();
        }

        let temp_lexer = Lexer {
            tokens: expr_tokens,
        };

        self.to_rpn(temp_lexer);
        self.build_ast();
        self.ast_expr.clone()
    }

    fn parse_block(&mut self, iter: &mut Peekable<Iter<Token>>) -> Vec<Expr> {
        let mut block = Vec::new();

        let mut brace_depth = 0;
        let mut expr_tokens = Vec::new();

        while let Some(token) = iter.peek() {
            if **token == Token::RCurly && brace_depth == 0 {
                iter.next(); // consume `}`
                break;
            }

            let token = iter.next().unwrap().clone();

            match token {
                Token::If => {
                    let e = self.pre_parse_if(iter);
                    expr_tokens.push(token);
                    block.push(e);
                    expr_tokens.clear();
                }
                Token::While => {
                    let e = self.pre_parse_while(iter);
                    expr_tokens.push(token);
                    block.push(e);
                    expr_tokens.clear();
                }
                Token::For => {
                    let e = self.pre_parse_for(iter);
                    expr_tokens.push(token);
                    block.push(e);
                    expr_tokens.clear();
                }
                Token::LCurly => {
                    brace_depth += 1;
                    expr_tokens.push(token);
                }
                Token::RCurly => {
                    brace_depth -= 1;
                    expr_tokens.push(token);
                    let temp_lexer = Lexer {
                        tokens: expr_tokens.clone(),
                    };
                    let e = self.parse_expression(&temp_lexer);
                    block.push(e);
                    expr_tokens.clear();
                }
                Token::Semicolon if brace_depth == 0 => {
                    expr_tokens.push(token);
                    let temp_lexer = Lexer {
                        tokens: expr_tokens.clone(),
                    };
                    let e = self.parse_expression(&temp_lexer);
                    block.push(e);
                    expr_tokens.clear();
                }
                _ => {
                    expr_tokens.push(token);
                }
            }
        }

        block
    }

    #[allow(clippy::vec_box)]
    fn parse_block_box(&mut self, iter: &mut Peekable<Iter<Token>>) -> Vec<Box<Expr>> {
        let mut block = Vec::new();

        let mut brace_depth = 0;
        let mut expr_tokens = Vec::new();

        while let Some(token) = iter.peek() {
            if **token == Token::RCurly && brace_depth == 0 {
                iter.next(); // consume `}`
                break;
            }

            let token = iter.next().unwrap().clone();

            match token {
                Token::If => {
                    let e = self.pre_parse_if(iter);
                    expr_tokens.push(token);
                    block.push(Box::new(e));
                    expr_tokens.clear();
                }
                Token::While => {
                    let e = self.pre_parse_while(iter);
                    expr_tokens.push(token);
                    block.push(Box::new(e));
                    expr_tokens.clear();
                }
                Token::For => {
                    let e = self.pre_parse_for(iter);
                    expr_tokens.push(token);
                    block.push(Box::new(e));
                    expr_tokens.clear();
                }
                Token::LCurly => {
                    brace_depth += 1;
                    expr_tokens.push(token);
                }
                Token::RCurly => {
                    brace_depth -= 1;
                    expr_tokens.push(token);
                    let temp_lexer = Lexer {
                        tokens: expr_tokens.clone(),
                    };
                    let e = self.parse_expression(&temp_lexer);
                    block.push(Box::new(e));
                    expr_tokens.clear();
                }
                Token::Semicolon if brace_depth == 0 => {
                    expr_tokens.push(token);
                    let temp_lexer = Lexer {
                        tokens: expr_tokens.clone(),
                    };
                    let e = self.parse_expression(&temp_lexer);
                    block.push(Box::new(e));
                    expr_tokens.clear();
                }
                _ => {
                    expr_tokens.push(token);
                }
            }
        }

        block
    }

    fn parse_if_expression(&mut self, iter: &mut Peekable<Iter<Token>>) -> Expr {
        // Accept both `if` and `elif` here
        match iter.next() {
            Some(Token::If) | Some(Token::Elif) => {}
            other => panic!("Expected `if` or `elif`, found {:?}", other),
        }

        let condition = self.parse_condition(iter); // Parse condition until `{`
        let body = self.parse_block(iter); // Parse `{ ... }`

        let else_branch = match iter.peek().copied() {
            Some(Token::Elif) => {
                Some(Box::new(self.parse_if_expression(iter))) // Recurse on `elif`
            }
            Some(Token::Else) => {
                iter.next(); // consume `else`
                let else_body = self.parse_block(iter);
                Some(Box::new(Expr::Else { body: else_body }))
            }
            _ => None,
        };

        Expr::If {
            condition: Box::new(condition),
            body,
            else_branch,
        }
    }

    fn parse_while_expression(&mut self, iter: &mut Peekable<Iter<Token>>) -> Expr {
        match iter.next() {
            Some(Token::While) => {}
            other => panic!("Expected 'while', found {:?}", other),
        }

        let condition = self.parse_condition_while(iter); // Parse condition until `{`
        let body = self.parse_block(iter); // Parse `{ ... }`

        Expr::While {
            condition: Box::new(condition),
            body,
        }
    }

    fn parse_for_expression(&mut self, iter: &mut Peekable<Iter<Token>>) -> Expr {
        match iter.next() {
            Some(Token::For) => {}
            other => panic!("Expected 'while', found {:?}", other),
        }

        let iter_start_name = self.parse_condition_for_init(iter); // Parse until `in`
        let to_iter_var = self.parse_condition_for_after(iter); // Parse until `{`
        let body = self.parse_block_box(iter); // Parse `{ ... }`

        /*Expr::For {
            iter_start_name,
            to_iter_var: Box::new(to_iter_var),
            body,
        }*/

        Expr::For {
            iter_start_name,
            iter_target: to_iter_var,
            body,
        }
    }

    #[allow(clippy::single_match)]
    #[allow(dead_code)]
    pub fn type_check(&self) {
        for func in self.functions.values() {
            for expr in func.body.clone() {
                match expr {
                    Expr::VarDecl {
                        name,
                        mutable: _,
                        type_name,
                        value,
                    } => {
                        let declared_type = self.type_str_to_enum(type_name);
                        let value_type = self.get_expr_type(&value);

                        if declared_type != value_type {
                            panic!(
                                "Type mismatch in let declaration for '{}': expected {:?}, got {:?}",
                                name, declared_type, value_type
                            );
                        }
                    }
                    _ => {}
                }
            }
        }
    }

    pub fn parse_let_expression(&mut self, tokens: &[Token]) -> Expr {
        let mut iter = tokens.iter().peekable();

        assert_eq!(iter.next(), Some(&Token::Let));

        let mutable = matches!(iter.clone().next(), Some(Token::Mut));
        if mutable {
            iter.next();
        }

        let name = match iter.next() {
            Some(Token::Ident(name)) => name.clone(),
            _ => panic!("Expected identifier after 'v'"),
        };

        let type_name = match iter.next() {
            Some(Token::Colon) => match iter.next() {
                Some(Token::Type(t)) => t.clone(),
                _ => panic!("Expected type after ':'"),
            },
            _ => panic!("Expected ':' after identifier"),
        };

        if self
            .utils
            .ensure_equal(iter.clone().next(), Some(&Token::InputOp))
            .is_err()
        {
            panic!("Expected '->'")
        }
        assert_eq!(iter.next(), Some(&Token::InputOp));

        if *iter.clone().last().unwrap() != Token::Semicolon {
            panic!("Expected ';' at end of line")
        }

        // Grab everything after the `->` for expression
        let mut expr_tokens: Vec<Token> = iter.cloned().collect();

        expr_tokens.remove(expr_tokens.len() - 1);
        let combined = combine_tokens(expr_tokens.iter().peekable());
        let mut temp_lexer = Lexer::new();
        temp_lexer.tokenize(&combined);

        self.to_rpn(temp_lexer.clone());
        self.build_ast();

        #[allow(unused_variables)]
        if let Expr::BinaryOp { .. } = &self.ast_expr.clone() {
        } else {
            let mut valid_type = true;
            if let Expr::FunctionCall { .. } = &self.ast_expr.clone() {
            } else if let Expr::Ident(v, _, _) = &self.ast_expr.clone() {
                valid_type = self.check_type(&type_name, self.variable_stack.get(v).unwrap());
            } else {
                valid_type = self.check_type(&type_name, &self.ast_expr.clone());
            }

            let e = &self.ast_expr.clone();
            if !valid_type {
                let t = &self.match_type(e).clone();
            }
        }

        let e = Expr::VarDecl {
            name: name.clone(),
            mutable,
            type_name: type_name.clone(),
            value: Box::new(self.ast_expr.clone()),
        };

        self.variable_types
            .insert(name.clone(), self.type_str_to_enum(type_name));

        self.variable_stack.insert(name.clone(), e.clone());

        e
    }

    pub fn get_expr_type(&self, expr: &Expr) -> Type {
        match expr {
            Expr::Value {
                value: Value::Int(_),
                ..
            } => Type::Int,
            Expr::Value {
                value: Value::Float(_),
                ..
            } => Type::Float,
            Expr::Value {
                value: Value::Bool(_),
                ..
            } => Type::Bool,
            Expr::Value {
                value: Value::Str(_),
                ..
            } => Type::Str,
            Expr::Value {
                value: Value::Null, ..
            } => Type::Null,

            Expr::InputMacro => Type::Str,

            Expr::Ident(name, _, _) => self
                .variable_types
                .get(name)
                .cloned()
                .unwrap_or_else(|| panic!("Unknown variable: {}", name)),

            Expr::FunctionCall { name, .. } => {
                let f = self
                    .functions
                    .get(name)
                    .unwrap_or_else(|| panic!("Unknown function: {}", name));
                f.return_type.clone()
            }

            Expr::BinaryOp { left, right, op } => self.get_bin_op_type(left, right, op),
            _ => Type::Null,
        }
    }

    pub fn get_bin_op_type(&self, left: &Expr, right: &Expr, op: &String) -> Type {
        let left_type = self.get_expr_type(left);
        let right_type = self.get_expr_type(right);
        if left_type != right_type {
            panic!(
                "Type mismatch in binary op: {:?} vs {:?}",
                left_type, right_type
            );
        }

        match op.as_str() {
            "+" | "-" | "*" | "/" | "%" => {
                if left_type == Type::Int || left_type == Type::Float {
                    left_type
                } else {
                    panic!("Invalid types for math op: {:?}", left_type);
                }
            }
            "::" | "!:" | ">" | "<" | ">:" | "<:" => Type::Bool,
            _ => panic!("Unknown operator {}", op),
        }
    }

    pub fn get_bin_op_value(&self, left: &Expr, op: &str) -> Value {
        let left_type = self.get_expr_type(left);

        match op {
            "+" | "-" | "*" | "/" | "%" => {
                if left_type == Type::Int {
                    Value::Int(0)
                } else if left_type == Type::Float {
                    Value::Float(0.0)
                } else {
                    panic!("Invalid types for math op: {:?}", left_type);
                }
            }
            "::" | "!:" | ">" | "<" | ">:" | "<:" => Value::Bool(false),
            _ => Value::Null,
        }
    }

    #[allow(dead_code)]
    pub fn get_type_str(&mut self, value: &Value) -> &str {
        match value {
            Value::Int(_) => "int",
            Value::Bool(_) => "bool",
            Value::Str(_) => "str",
            Value::Null => "null",
            Value::Float(_) => "float",
        }
    }

    #[allow(clippy::only_used_in_recursion)]
    pub fn match_type(&mut self, value: &Expr) -> Value {
        match value {
            Expr::Value { value, .. } => value.clone(),
            Expr::VarDecl { value: v, .. } => self.match_type(v),
            Expr::FunctionCall { name, .. } => {
                match &self.functions.get(name).unwrap().return_type {
                    Type::Int => Value::Int(0),
                    Type::Float => Value::Float(0.0),
                    Type::Bool => Value::Bool(false),
                    Type::Str => Value::Str("".to_string()),
                    Type::Null => Value::Null,
                }
            }
            Expr::Ident(v, _, _) => {
                let t = self
                    .variable_types
                    .get(v)
                    .unwrap_or_else(|| panic!("Cannot find variable type for '{}'", v));
                match t {
                    Type::Int => Value::Int(0),
                    Type::Float => Value::Float(0.0),
                    Type::Bool => Value::Bool(false),
                    Type::Str => Value::Str("".to_string()),
                    Type::Null => Value::Null,
                }
            }
            Expr::Cast { target_type, .. } => match target_type {
                Type::Int => Value::Int(0),
                Type::Float => Value::Float(0.0),
                Type::Bool => Value::Bool(false),
                Type::Str => Value::Str("".to_string()),
                Type::Null => Value::Null,
            },
            Expr::InputMacro => Value::Str("".to_string()),
            _ => {
                panic!("Matched type against nothing (internal error)")
            }
        }
    }

    #[allow(clippy::ptr_arg)]
    #[allow(clippy::borrowed_box)]
    #[allow(dead_code)]
    pub fn bin_op(&mut self, op: &String, l: Value, r: Value) -> Value {
        if op.as_str() == "/" && r == Value::Int(0) {
            panic!("Cannot divide by 0")
        }
        if op.as_str() == "%" && r == Value::Int(0) {
            panic!("Modulo by 0 is not allowed")
        }
        match (op.as_str(), l, r) {
            ("+", Value::Int(a), Value::Int(b)) => Value::Int(a + b),
            ("-", Value::Int(a), Value::Int(b)) => Value::Int(a - b),
            ("*", Value::Int(a), Value::Int(b)) => Value::Int(a * b),
            ("/", Value::Int(a), Value::Int(b)) => Value::Int(a / b),
            ("%", Value::Int(a), Value::Int(b)) => Value::Int(a % b),

            ("+", Value::Float(a), Value::Float(b)) => Value::Float(a + b),
            ("-", Value::Float(a), Value::Float(b)) => Value::Float(a - b),
            ("*", Value::Float(a), Value::Float(b)) => Value::Float(a * b),
            ("/", Value::Float(a), Value::Float(b)) => Value::Float(a / b),
            ("%", Value::Float(a), Value::Float(b)) => Value::Float(a % b),

            ("+", Value::Str(a), Value::Str(b)) => Value::Str(a + &b),

            ("::", Value::Int(a), Value::Int(b)) => Value::Bool(a == b),
            ("::", Value::Float(a), Value::Float(b)) => Value::Bool(a == b),
            ("::", Value::Str(a), Value::Str(b)) => Value::Bool(a == b),
            ("::", Value::Bool(a), Value::Bool(b)) => Value::Bool(a == b),
            ("::", Value::Null, Value::Null) => Value::Bool(true),

            ("!:", Value::Int(a), Value::Int(b)) => Value::Bool(a != b),
            ("!:", Value::Float(a), Value::Float(b)) => Value::Bool(a != b),
            ("!:", Value::Str(a), Value::Str(b)) => Value::Bool(a != b),
            ("!:", Value::Bool(a), Value::Bool(b)) => Value::Bool(a != b),
            ("!:", Value::Null, Value::Null) => Value::Bool(false),

            (">", Value::Int(a), Value::Int(b)) => Value::Bool(a > b),
            ("<", Value::Int(a), Value::Int(b)) => Value::Bool(a < b),
            (">:", Value::Int(a), Value::Int(b)) => Value::Bool(a >= b),
            ("<:", Value::Int(a), Value::Int(b)) => Value::Bool(a <= b),

            (">", Value::Float(a), Value::Float(b)) => Value::Bool(a > b),
            ("<", Value::Float(a), Value::Float(b)) => Value::Bool(a < b),
            (">:", Value::Float(a), Value::Float(b)) => Value::Bool(a >= b),
            ("<:", Value::Float(a), Value::Float(b)) => Value::Bool(a <= b),

            ("&&", Value::Bool(a), Value::Bool(b)) => Value::Bool(a && b),
            ("||", Value::Bool(a), Value::Bool(b)) => Value::Bool(a || b),
            _ => panic!("Unsupported operation or type mismatch"),
        }
    }

    pub fn first_pass(&mut self, lexer: &Lexer) {
        let tokens = &lexer.tokens;
        let mut i = 0;

        while i < tokens.len() {
            match &tokens[i] {
                Token::MacroDefine => {
                    i += 1;
                    let mut extern_func = ExternFunction {
                        name: String::new(),
                        file: String::new(),
                    };

                    if let Token::Ident(name) = &tokens[i] {
                        extern_func.name = name.to_string();
                        i += 1;
                    } else {
                        panic!("Expected extern macro name")
                    }

                    if let Token::OutputOp = &tokens[i] {
                        i += 1;
                    } else {
                        panic!("Expected output operator in macro define")
                    }

                    if let Token::Str(s) = &tokens[i] {
                        extern_func.file = s.to_string();
                        i += 1;
                    } else {
                        panic!("Expected string for .rs file name in macro define")
                    }

                    if let Token::Semicolon = &tokens[i] {
                        i += 1;
                    } else {
                        panic!("Expected ;")
                    }

                    self.extern_funcs.push(extern_func);
                }
                Token::Fn => {
                    let start = i;
                    let mut brace_depth = 0;

                    while i < tokens.len() {
                        match &tokens[i] {
                            Token::LCurly => brace_depth += 1,
                            Token::RCurly => {
                                brace_depth -= 1;
                                if brace_depth == 0 {
                                    i += 1;
                                    break;
                                }
                            }
                            _ => {}
                        }
                        i += 1;
                    }

                    let func_tokens = &tokens[start..i]; // slice with full function declaration

                    self.variable_types.clear();
                    self.parse_function_definition(func_tokens);
                }
                _ => {
                    // skip to next token if it's not a top-level construct you care about
                    i += 1;
                }
            }
        }
    }

    pub fn parse_expression(&mut self, lexer: &Lexer) -> Expr {
        let tokens = &lexer.tokens;
        let mut iter = tokens.iter().peekable();

        match iter.peek() {
            Some(Token::Let) => self.parse_let_expression(tokens),
            Some(Token::If) => self.parse_if_expression(&mut iter),
            Some(Token::While) => self.parse_while_expression(&mut iter),
            Some(Token::For) => self.parse_for_expression(&mut iter),
            Some(Token::Ident(_)) => self.parse_var_update(tokens),
            #[allow(suspicious_double_ref_op)]
            Some(Token::Number(_)) => {
                let tokens = vec![iter.peek().unwrap().clone().to_owned()];
                let temp_lexer = Lexer { tokens };
                self.to_rpn(temp_lexer.clone());
                self.build_ast();

                match self.ast_expr.clone() {
                    Expr::Value { .. } => self.ast_expr.clone(),
                    _ => {
                        panic!("Invalid AST Expression")
                    }
                }
            }
            #[allow(suspicious_double_ref_op)]
            Some(Token::Float(_)) => {
                let tokens = vec![iter.peek().unwrap().clone().to_owned()];
                let temp_lexer = Lexer { tokens };
                self.to_rpn(temp_lexer.clone());
                self.build_ast();
                match self.ast_expr.clone() {
                    Expr::Value { .. } => self.ast_expr.clone(),
                    _ => {
                        panic!("Invalid AST Expression")
                    }
                }
            }
            #[allow(suspicious_double_ref_op)]
            Some(Token::Str(_)) => {
                let tokens = vec![iter.peek().unwrap().clone().to_owned()];
                let temp_lexer = Lexer { tokens };
                self.to_rpn(temp_lexer.clone());
                self.build_ast();
                match self.ast_expr.clone() {
                    Expr::Value { .. } => self.ast_expr.clone(),
                    _ => {
                        panic!("Invalid AST Expression")
                    }
                }
            }
            Some(Token::CustomMacroCall(name, body)) => Expr::CustomMacro {
                name: name.to_string(),
                args: self.parse_function_arguments(body, false),
            },
            Some(Token::FunctionCall(_, _)) => self.parse_function_call(tokens, false, false),
            Some(Token::OutputOp) => self.parse_return(tokens),
            Some(Token::PrintLn) => self.parse_println(tokens),
            Some(Token::PrintSingle) => self.parse_printsingle(tokens),
            Some(Token::SuperPrint) => self.parse_super_print(tokens),
            Some(Token::InputMacro) => self.parse_input_macro(tokens, true),
            Some(Token::Fn) => Expr::Value {
                value: Value::Null,
                is_negate_not: false,
                is_negate_minus: false,
            },
            Some(Token::Sleep) => self.parse_sleep(tokens),

            _ => {
                panic!("Unexpected Expression {:?}", iter.peek())
            }
        }
    }

    pub fn parse_input_macro(&mut self, tokens: &[Token], is_final: bool) -> Expr {
        let mut iter = tokens.iter().peekable();

        assert_eq!(iter.next(), Some(&Token::InputMacro));

        #[allow(clippy::collapsible_if)]
        if is_final {
            if *iter.clone().last().unwrap() != Token::Semicolon {
                panic!("Expected ';' at end of line")
            }
        }

        Expr::InputMacro
    }

    pub fn parse_cast_value(&mut self, tokens: &[Token]) -> Expr {
        let iter = tokens.iter().peekable();

        let mut expr_tokens = Vec::new();

        for token in iter {
            match token {
                Token::Comma => break,
                _ => expr_tokens.push(token.clone()),
            }
        }

        let expr_lexer = Lexer {
            tokens: expr_tokens.to_vec(),
        };
        self.to_rpn(expr_lexer.clone());
        self.build_ast();
        self.ast_expr.clone()
    }

    pub fn parse_cast_type(&mut self, tokens: &[Token]) -> Type {
        let iter = tokens.iter().peekable();

        let mut expr_tokens = Vec::new();

        for token in iter {
            match token {
                Token::RParen => break,
                _ => expr_tokens.push(token.clone()),
            }
        }

        match &expr_tokens[0] {
            Token::Type(s) if s == "int" => Type::Int,
            Token::Type(s) if s == "float" => Type::Float,
            Token::Type(s) if s == "bool" => Type::Bool,
            Token::Type(s) if s == "str" => Type::Str,
            Token::Type(s) if s == "null" => Type::Null,
            _ => panic!("Unknown type '{:?}'", expr_tokens[0]),
        }
    }

    /*pub fn parse_cast(&mut self, tokens: &[Token]) -> Expr {
        let mut iter = tokens.iter().peekable();

        iter.next();

        let mut inner_tokens = Vec::new();
        let mut paren_depth = 1;

        for token in iter {
            match token {
                Token::LParen => {
                    paren_depth += 1;
                    inner_tokens.push(token.clone());
                }
                Token::RParen => {
                    paren_depth -= 1;
                    if paren_depth == 0 {
                        break;
                    } else {
                        inner_tokens.push(token.clone());
                    }
                }
                _ => inner_tokens.push(token.clone()),
            }
        }

        // Split at comma
        let comma_index = inner_tokens
            .iter()
            .position(|t| *t == Token::Comma)
            .expect("Expected ',' between expression and type");

        let expr_tokens = &inner_tokens[0..comma_index];
        let type_tokens = &inner_tokens[comma_index + 1..];

        let expr_lexer = Lexer {
            tokens: expr_tokens.to_vec(),
        };
        self.to_rpn(expr_lexer.clone());
        self.build_ast();
        let expr = self.ast_expr.clone();

        if type_tokens.len() != 1 {
            panic!("Expected single type identifier after ','");
        }

        let target_type = match &type_tokens[0] {
            Token::Type(s) if s == "int" => Type::Int,
            Token::Type(s) if s == "float" => Type::Float,
            Token::Type(s) if s == "bool" => Type::Bool,
            Token::Type(s) if s == "str" => Type::Str,
            Token::Type(s) if s == "null" => Type::Null,
            _ => panic!("Unknown type '{:?}'", type_tokens[0]),
        };

        Expr::Cast {
            expr: Box::new(expr),
            target_type,
        }
    }*/

    pub fn parse_println(&mut self, tokens: &[Token]) -> Expr {
        let mut iter = tokens.iter().peekable();

        assert_eq!(iter.next(), Some(&Token::PrintLn));

        if self
            .utils
            .ensure_equal(iter.clone().next(), Some(&Token::LParen))
            .is_err()
        {
            panic!("Expected '('")
        }
        assert_eq!(iter.next(), Some(&Token::LParen));

        if *iter.clone().last().unwrap() != Token::Semicolon {
            panic!("Expected ';' at end of line")
        }

        let mut inner_tokens = Vec::new();
        let mut paren_depth = 1;

        for token in iter {
            match token {
                Token::LParen => {
                    paren_depth += 1;
                    inner_tokens.push(token.clone());
                }
                Token::RParen => {
                    paren_depth -= 1;
                    if paren_depth == 0 {
                        break;
                    } else {
                        inner_tokens.push(token.clone());
                    }
                }
                _ => inner_tokens.push(token.clone()),
            }
        }

        let temp_lexer = Lexer {
            tokens: inner_tokens.clone(),
        };
        self.to_rpn(temp_lexer.clone());
        self.build_ast();

        Expr::PrintLn(Box::new(self.ast_expr.clone()))
    }

    pub fn parse_super_print(&mut self, tokens: &[Token]) -> Expr {
        let mut iter = tokens.iter().peekable();

        assert_eq!(iter.next(), Some(&Token::SuperPrint));

        if self
            .utils
            .ensure_equal(iter.clone().next(), Some(&Token::LParen))
            .is_err()
        {
            panic!("Expected '('")
        }
        assert_eq!(iter.next(), Some(&Token::LParen));

        if *iter.clone().last().unwrap() != Token::Semicolon {
            panic!("Expected ';' at end of line")
        }

        let mut inner_tokens = Vec::new();
        let mut paren_depth = 1;

        for token in iter {
            match token {
                Token::LParen => {
                    paren_depth += 1;
                    inner_tokens.push(token.clone());
                }
                Token::RParen => {
                    paren_depth -= 1;
                    if paren_depth == 0 {
                        break;
                    } else {
                        inner_tokens.push(token.clone());
                    }
                }
                _ => inner_tokens.push(token.clone()),
            }
        }

        let temp_lexer = Lexer {
            tokens: inner_tokens.clone(),
        };
        self.to_rpn(temp_lexer.clone());
        self.build_ast();

        Expr::SuperPrint(Box::new(self.ast_expr.clone()))
    }

    pub fn parse_printsingle(&mut self, tokens: &[Token]) -> Expr {
        let mut iter = tokens.iter().peekable();

        assert_eq!(iter.next(), Some(&Token::PrintSingle));

        if self
            .utils
            .ensure_equal(iter.clone().next(), Some(&Token::LParen))
            .is_err()
        {
            panic!("Expected '('")
        }
        assert_eq!(iter.next(), Some(&Token::LParen));

        if *iter.clone().last().unwrap() != Token::Semicolon {
            panic!("Expected ';' at end of line")
        }

        let mut inner_tokens = Vec::new();
        let mut paren_depth = 1;

        for token in iter {
            match token {
                Token::LParen => {
                    paren_depth += 1;
                    inner_tokens.push(token.clone());
                }
                Token::RParen => {
                    paren_depth -= 1;
                    if paren_depth == 0 {
                        break;
                    } else {
                        inner_tokens.push(token.clone());
                    }
                }
                _ => inner_tokens.push(token.clone()),
            }
        }

        let temp_lexer = Lexer {
            tokens: inner_tokens.clone(),
        };
        self.to_rpn(temp_lexer.clone());
        self.build_ast();

        Expr::PrintSingle(Box::new(self.ast_expr.clone()))
    }

    pub fn parse_sleep(&mut self, tokens: &[Token]) -> Expr {
        let mut iter = tokens.iter().peekable();

        assert_eq!(iter.next(), Some(&Token::Sleep));

        if self
            .utils
            .ensure_equal(iter.clone().next(), Some(&Token::LParen))
            .is_err()
        {
            panic!("Expected '('")
        }
        assert_eq!(iter.next(), Some(&Token::LParen));

        if *iter.clone().last().unwrap() != Token::Semicolon {
            panic!("Expected ';' at end of line")
        }

        let mut inner_tokens = Vec::new();
        let mut paren_depth = 1;

        for token in iter {
            match token {
                Token::LParen => {
                    paren_depth += 1;
                    inner_tokens.push(token.clone());
                }
                Token::RParen => {
                    paren_depth -= 1;
                    if paren_depth == 0 {
                        break;
                    } else {
                        inner_tokens.push(token.clone());
                    }
                }
                _ => inner_tokens.push(token.clone()),
            }
        }

        let temp_lexer = Lexer {
            tokens: inner_tokens.clone(),
        };
        self.to_rpn(temp_lexer.clone());
        self.build_ast();

        Expr::Sleep(Box::new(self.ast_expr.clone()))
    }

    pub fn check_type(&self, expected: &str, value: &Expr) -> bool {
        let mut v2 = value.clone();
        if let Expr::VarDecl { value: v3, .. } = value {
            if let Expr::BinaryOp { op, left, .. } = *v3.clone() {
                v2 = Expr::Value {
                    value: self.get_bin_op_value(&left, &op),
                    is_negate_not: false,
                    is_negate_minus: false,
                };
            }
        }
        matches!(
            (expected, v2),
            (
                "int",
                Expr::Value {
                    value: Value::Int(_),
                    ..
                }
            ) | (
                "float",
                Expr::Value {
                    value: Value::Float(_),
                    ..
                }
            ) | (
                "bool",
                Expr::Value {
                    value: Value::Bool(_),
                    ..
                }
            ) | (
                "str",
                Expr::Value {
                    value: Value::Str(_),
                    ..
                }
            ) | ("str", Expr::InputMacro)
                | (
                    "null",
                    Expr::Value {
                        value: Value::Null,
                        ..
                    }
                )
        )
    }

    pub fn type_str_to_enum(&self, t: String) -> Type {
        match t.as_str() {
            "int" => Type::Int,
            "str" => Type::Str,
            "bool" => Type::Bool,
            "float" => Type::Float,
            "null" => Type::Null,
            _ => Type::Null,
        }
    }

    #[allow(dead_code)]
    pub fn type_enum_to_str(&self, t: Type) -> String {
        match t {
            Type::Int => "int".to_string(),
            Type::Float => "float".to_string(),
            Type::Bool => "bool".to_string(),
            Type::Str => "str".to_string(),
            Type::Null => "null".to_string(),
        }
    }
}
