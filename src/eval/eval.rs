use std::{collections::HashMap, io};

use crate::{
    general::ast::{Expr, Type, Value},
    parser::parser::{Function, Parser},
};

pub fn eval_var_update(parser: &mut Parser, expr: &Expr) -> Value {
    if let Expr::VarUpdate { var, new_value } = expr {
        let evaluated_value = eval_ast(parser, new_value);
        let evaluated_expr = Expr::Value(evaluated_value.clone().0);

        // Temporarily extract everything we need and clone what we must
        let (is_mutable, expected_type_str) = {
            let stored_expr = parser
                .variable_stack
                .get(var)
                .unwrap_or_else(|| panic!("Variable '{}' not in scope", var));
            match stored_expr {
                Expr::VarDecl {
                    mutable, type_name, ..
                } => (*mutable, type_name.clone()),
                _ => panic!("Variable '{}' is not assignable", var),
            }
        };

        if !is_mutable {
            panic!("Variable '{}' is not mutable", var);
        }

        // Safe now: no borrows are alive
        let valid_type = parser.check_type(&expected_type_str, &evaluated_expr);
        if !valid_type {
            let t = &parser.match_type(&evaluated_expr);
            panic!(
                "Type mismatch: tried assigning value of type '{}' to '{}'",
                parser.get_type_str(t),
                expected_type_str
            );
        }

        // Now re-borrow mutably *after* the type check
        if let Some(Expr::VarDecl { value, .. }) = parser.variable_stack.get_mut(var) {
            *value = Box::new(evaluated_expr);
        }

        evaluated_value.0
    } else {
        panic!("eval_var_update called with non-VarUpdate expression");
    }
}

pub fn eval_for(parser: &mut Parser, expr: &Expr) -> (Value, bool) {
    match expr {
        Expr::For {
            iter_start_name,
            to_iter_var,
            body,
        } => {
            parser.in_loop = true;
            //let mut cond_val = eval_ast(parser, condition);
            let iter_start_expr = iter_start_name;
            let to_iter_expr = *to_iter_var.clone();

            let mut return_val = Value::Null;

            match to_iter_expr {
                Expr::Ident(_, _, _) => {
                    let v = eval_ast(parser, &to_iter_expr);
                    match v.0 {
                        Value::Int(i) => {
                            let mut new_vars: HashMap<&String, &Box<Expr>> = HashMap::new();
                            let mut old_vars = parser.variable_stack.clone();

                            for n in 0..i {
                                parser.variable_stack.insert(
                                    iter_start_expr.to_string(),
                                    Expr::VarDecl {
                                        name: iter_start_expr.to_string(),
                                        mutable: false,
                                        type_name: "int".to_string(),
                                        value: Box::new(Expr::Value(Value::Int(n))),
                                    },
                                );
                                for expr in body {
                                    let result = eval_ast(parser, expr);
                                    if let Expr::Return(_) = expr {
                                        return_val = result.0;

                                        parser.variable_stack = old_vars;
                                        parser.returned_if = true;
                                        parser.final_return = (return_val, true);
                                        return parser.final_return.clone();
                                    }

                                    if let Expr::VarDecl { name, value, .. } = expr {
                                        new_vars.insert(name, value);
                                    }

                                    if parser.returned_if {
                                        return parser.final_return.clone();
                                    }
                                }
                                for v in &new_vars {
                                    if parser.variable_stack.contains_key(&v.0.to_string()) {
                                        parser.variable_stack.remove(&v.0.to_string());
                                    }
                                }
                            }

                            for v in &parser.variable_stack {
                                if old_vars.contains_key(v.0) {
                                    old_vars.insert(v.0.to_owned(), v.1.to_owned());
                                }
                            }
                            parser.variable_stack = old_vars; // restore outer scope
                        }
                        Value::Float(_) => {
                            panic!("Cannot iter over floating point value!");
                        }
                        Value::Bool(_) => {
                            panic!("Cannot iter over boolean value!");
                        }
                        Value::Str(s) => {
                            let mut new_vars: HashMap<&String, &Box<Expr>> = HashMap::new();
                            let mut old_vars = parser.variable_stack.clone();

                            for n in s.chars() {
                                parser.variable_stack.insert(
                                    iter_start_expr.to_string(),
                                    Expr::VarDecl {
                                        name: iter_start_expr.to_string(),
                                        mutable: false,
                                        type_name: "str".to_string(),
                                        value: Box::new(Expr::Value(Value::Str(n.to_string()))),
                                    },
                                );
                                for expr in body {
                                    let result = eval_ast(parser, expr);
                                    if let Expr::Return(_) = expr {
                                        return_val = result.0;

                                        parser.variable_stack = old_vars;
                                        parser.returned_if = true;
                                        parser.final_return = (return_val, true);
                                        return parser.final_return.clone();
                                    }

                                    if let Expr::VarDecl { name, value, .. } = expr {
                                        new_vars.insert(name, value);
                                    }

                                    if parser.returned_if {
                                        return parser.final_return.clone();
                                    }
                                }
                                for v in &new_vars {
                                    if parser.variable_stack.contains_key(&v.0.to_string()) {
                                        parser.variable_stack.remove(&v.0.to_string());
                                    }
                                }
                            }

                            for v in &parser.variable_stack {
                                if old_vars.contains_key(v.0) {
                                    old_vars.insert(v.0.to_owned(), v.1.to_owned());
                                }
                            }
                            parser.variable_stack = old_vars; // restore outer scope
                        }
                        Value::Null => {
                            panic!("Cannot iter over null value!");
                        }
                    }
                }
                Expr::Value(value) => {
                    match value {
                        Value::Int(i) => {
                            let mut new_vars: HashMap<&String, &Box<Expr>> = HashMap::new();
                            let mut old_vars = parser.variable_stack.clone();

                            for n in 0..i {
                                parser.variable_stack.insert(
                                    iter_start_expr.to_string(),
                                    Expr::VarDecl {
                                        name: iter_start_expr.to_string(),
                                        mutable: false,
                                        type_name: "int".to_string(),
                                        value: Box::new(Expr::Value(Value::Int(n))),
                                    },
                                );
                                for expr in body {
                                    let result = eval_ast(parser, expr);
                                    if let Expr::Return(_) = expr {
                                        return_val = result.0;

                                        parser.variable_stack = old_vars;
                                        parser.returned_if = true;
                                        parser.final_return = (return_val, true);
                                        return parser.final_return.clone();
                                    }

                                    if let Expr::VarDecl { name, value, .. } = expr {
                                        new_vars.insert(name, value);
                                    }

                                    if parser.returned_if {
                                        return parser.final_return.clone();
                                    }
                                }
                                for v in &new_vars {
                                    if parser.variable_stack.contains_key(&v.0.to_string()) {
                                        parser.variable_stack.remove(&v.0.to_string());
                                    }
                                }
                            }

                            for v in &parser.variable_stack {
                                if old_vars.contains_key(v.0) {
                                    old_vars.insert(v.0.to_owned(), v.1.to_owned());
                                }
                            }
                            parser.variable_stack = old_vars; // restore outer scope
                        }
                        Value::Float(_) => {
                            panic!("Cannot iter over floating point value!");
                        }
                        Value::Bool(_) => {
                            panic!("Cannot iter over boolean value!");
                        }
                        Value::Str(s) => {
                            let mut new_vars: HashMap<&String, &Box<Expr>> = HashMap::new();
                            let mut old_vars = parser.variable_stack.clone();

                            for n in s.chars() {
                                parser.variable_stack.insert(
                                    iter_start_expr.to_string(),
                                    Expr::VarDecl {
                                        name: iter_start_expr.to_string(),
                                        mutable: false,
                                        type_name: "str".to_string(),
                                        value: Box::new(Expr::Value(Value::Str(n.to_string()))),
                                    },
                                );
                                for expr in body {
                                    let result = eval_ast(parser, expr);
                                    if let Expr::Return(_) = expr {
                                        return_val = result.0;

                                        parser.variable_stack = old_vars;
                                        parser.returned_if = true;
                                        parser.final_return = (return_val, true);
                                        return parser.final_return.clone();
                                    }

                                    if let Expr::VarDecl { name, value, .. } = expr {
                                        new_vars.insert(name, value);
                                    }

                                    if parser.returned_if {
                                        return parser.final_return.clone();
                                    }
                                }
                                for v in &new_vars {
                                    if parser.variable_stack.contains_key(&v.0.to_string()) {
                                        parser.variable_stack.remove(&v.0.to_string());
                                    }
                                }
                            }

                            for v in &parser.variable_stack {
                                if old_vars.contains_key(v.0) {
                                    old_vars.insert(v.0.to_owned(), v.1.to_owned());
                                }
                            }
                            parser.variable_stack = old_vars; // restore outer scope
                        }
                        Value::Null => {
                            panic!("Cannot iter over null value!");
                        }
                    }
                }
                Expr::FunctionCall { .. } => {
                    let v = eval_ast(parser, &to_iter_expr);
                    match v.0 {
                        Value::Int(i) => {
                            let mut new_vars: HashMap<&String, &Box<Expr>> = HashMap::new();
                            let mut old_vars = parser.variable_stack.clone();

                            for n in 0..i {
                                parser.variable_stack.insert(
                                    iter_start_expr.to_string(),
                                    Expr::VarDecl {
                                        name: iter_start_expr.to_string(),
                                        mutable: false,
                                        type_name: "int".to_string(),
                                        value: Box::new(Expr::Value(Value::Int(n))),
                                    },
                                );
                                for expr in body {
                                    let result = eval_ast(parser, expr);
                                    if let Expr::Return(_) = expr {
                                        return_val = result.0;

                                        parser.variable_stack = old_vars;
                                        parser.returned_if = true;
                                        parser.final_return = (return_val, true);
                                        return parser.final_return.clone();
                                    }

                                    if let Expr::VarDecl { name, value, .. } = expr {
                                        new_vars.insert(name, value);
                                    }

                                    if parser.returned_if {
                                        return parser.final_return.clone();
                                    }
                                }
                                for v in &new_vars {
                                    if parser.variable_stack.contains_key(&v.0.to_string()) {
                                        parser.variable_stack.remove(&v.0.to_string());
                                    }
                                }
                            }

                            for v in &parser.variable_stack {
                                if old_vars.contains_key(v.0) {
                                    old_vars.insert(v.0.to_owned(), v.1.to_owned());
                                }
                            }
                            parser.variable_stack = old_vars; // restore outer scope
                        }
                        Value::Float(_) => {
                            panic!("Cannot iter over floating point value!");
                        }
                        Value::Bool(_) => {
                            panic!("Cannot iter over boolean value!");
                        }
                        Value::Str(s) => {
                            let mut new_vars: HashMap<&String, &Box<Expr>> = HashMap::new();
                            let mut old_vars = parser.variable_stack.clone();

                            for n in s.chars() {
                                parser.variable_stack.insert(
                                    iter_start_expr.to_string(),
                                    Expr::VarDecl {
                                        name: iter_start_expr.to_string(),
                                        mutable: false,
                                        type_name: "str".to_string(),
                                        value: Box::new(Expr::Value(Value::Str(n.to_string()))),
                                    },
                                );
                                for expr in body {
                                    let result = eval_ast(parser, expr);
                                    if let Expr::Return(_) = expr {
                                        return_val = result.0;

                                        parser.variable_stack = old_vars;
                                        parser.returned_if = true;
                                        parser.final_return = (return_val, true);
                                        return parser.final_return.clone();
                                    }

                                    if let Expr::VarDecl { name, value, .. } = expr {
                                        new_vars.insert(name, value);
                                    }

                                    if parser.returned_if {
                                        return parser.final_return.clone();
                                    }
                                }
                                for v in &new_vars {
                                    if parser.variable_stack.contains_key(&v.0.to_string()) {
                                        parser.variable_stack.remove(&v.0.to_string());
                                    }
                                }
                            }

                            for v in &parser.variable_stack {
                                if old_vars.contains_key(v.0) {
                                    old_vars.insert(v.0.to_owned(), v.1.to_owned());
                                }
                            }
                            parser.variable_stack = old_vars; // restore outer scope
                        }
                        Value::Null => {
                            panic!("Cannot iter over null value!");
                        }
                    }
                }
                _ => {}
            }

            parser.in_loop = false;

            parser.final_return = (return_val, false);
            parser.final_return.clone()
        }
        _ => {
            panic!("Attempted to evaluate a non-while in an while statement")
        }
    }
}

pub fn eval_while(parser: &mut Parser, expr: &Expr) -> (Value, bool) {
    match expr {
        Expr::While { condition, body } => {
            parser.in_loop = true;
            let mut cond_val = eval_ast(parser, condition);

            let mut return_val = Value::Null;

            match cond_val.0 {
                Value::Bool(true) => {
                    let mut new_vars: HashMap<&String, &Box<Expr>> = HashMap::new();
                    let mut old_vars = parser.variable_stack.clone();

                    while cond_val.0 == Value::Bool(true) {
                        for expr in body {
                            let result = eval_ast(parser, expr);
                            if let Expr::Return(_) = expr {
                                return_val = result.0;

                                parser.variable_stack = old_vars;
                                parser.returned_if = true;
                                parser.final_return = (return_val, true);
                                return parser.final_return.clone();
                            }

                            if let Expr::VarDecl { name, value, .. } = expr {
                                new_vars.insert(name, value);
                            }

                            if parser.returned_if {
                                return parser.final_return.clone();
                            }
                        }
                        for v in &new_vars {
                            if parser.variable_stack.contains_key(&v.0.to_string()) {
                                parser.variable_stack.remove(&v.0.to_string());
                            }
                        }
                        cond_val = eval_ast(parser, condition);
                    }
                    for v in &parser.variable_stack {
                        if old_vars.contains_key(v.0) {
                            old_vars.insert(v.0.to_owned(), v.1.to_owned());
                        }
                    }
                    parser.variable_stack = old_vars; // restore outer scope
                }
                _ => {} //panic!("Condition in if statement must evaluate to bool"),
            }

            parser.in_loop = false;

            parser.final_return = (return_val, false);
            parser.final_return.clone()
        }
        _ => {
            panic!("Attempted to evaluate a non-while in an while statement")
        }
    }
}

pub fn eval_if(parser: &mut Parser, expr: &Expr) -> (Value, bool) {
    match expr {
        Expr::If {
            condition,
            body,
            else_branch,
        } => {
            let cond_val = eval_ast(parser, condition);

            let mut return_val = Value::Null;

            match cond_val.0 {
                Value::Bool(true) => {
                    let old_vars = parser.variable_stack.clone();
                    for expr in body {
                        let result = eval_ast(parser, expr);
                        if let Expr::Return(_) = expr {
                            return_val = result.0;
                            parser.variable_stack = old_vars;
                            parser.returned_if = true;
                            parser.final_return = (return_val, true);
                            return parser.final_return.clone();
                        }
                        if parser.returned_if {
                            return parser.final_return.clone();
                        }
                    }
                    if !parser.in_loop {
                        parser.variable_stack = old_vars; // restore outer scope
                    }
                }
                Value::Bool(false) => {
                    if let Some(else_expr) = else_branch {
                        return eval_ast(parser, else_expr);
                    }
                }
                _ => {} //panic!("Condition in if statement must evaluate to bool"),
            }

            parser.final_return = (return_val, false);
            parser.final_return.clone()
        }
        Expr::Else { body } => {
            let mut return_val = Value::Null;
            let old_vars = parser.variable_stack.clone();
            for expr in body {
                let result = eval_ast(parser, expr);
                if let Expr::Return(_) = expr {
                    return_val = result.0;
                    parser.variable_stack = old_vars;
                    parser.returned_if = true;
                    parser.final_return = (return_val.clone(), true);
                    return (return_val, true);
                }
            }
            if !parser.in_loop {
                parser.variable_stack = old_vars; // restore outer scope
            }
            parser.final_return = (return_val.clone(), false);
            (return_val, false)
        }
        _ => {
            panic!("Attempted to evaluate a non-if in an if statement")
        }
    }
}

#[allow(clippy::only_used_in_recursion)]
pub fn eval_ast(parser: &mut Parser, expr: &Expr) -> (Value, bool) {
    let result = match expr {
        Expr::Sleep(time_expr) => match *time_expr.clone() {
            Expr::Ident(..) => {
                let val = eval_ast(parser, time_expr);
                match val.0 {
                    Value::Float(f) => {
                        std::thread::sleep(std::time::Duration::from_secs_f64(f));
                        (Value::Null, false)
                    }
                    _ => {
                        panic!("Cannot evaluate sleep (zzz!) from non floating point")
                    }
                }
            }
            Expr::Value(val) => match val {
                Value::Float(f) => {
                    std::thread::sleep(std::time::Duration::from_secs_f64(f));
                    (Value::Null, false)
                }
                _ => {
                    panic!("Cannot evaluate sleep (zzz!) from non floating point")
                }
            },
            _ => {
                panic!("Invalid sleep (zzz!) value (expected float)")
            }
        },
        Expr::InputMacro => {
            let mut buffer = String::new();
            io::stdin().read_line(&mut buffer).unwrap();
            let input = buffer.trim();
            (Value::Str(input.to_string()), false)
        }
        Expr::While { .. } => eval_while(parser, expr),
        Expr::For { .. } => eval_for(parser, expr),
        Expr::If { .. } => eval_if(parser, expr),
        Expr::Else { .. } => eval_if(parser, expr),
        Expr::Ident(name, is_negate_not, is_negate_minus) => {
            match parser.variable_stack.clone().get(name) {
                Some(Expr::Value(val)) => match val {
                    Value::Int(i) => {
                        if *is_negate_minus {
                            (Value::Int(-i), false)
                        } else {
                            (val.clone(), false)
                        }
                    }
                    Value::Float(f) => {
                        if *is_negate_minus {
                            (Value::Float(-f), false)
                        } else {
                            (val.clone(), false)
                        }
                    }
                    Value::Bool(b) => {
                        if *is_negate_not {
                            (Value::Bool(!b), false)
                        } else {
                            (val.clone(), false)
                        }
                    }
                    Value::Str(_) => (val.clone(), false),
                    Value::Null => (val.clone(), false),
                },
                Some(Expr::BinaryOp { op, left, right }) => (parser.bin_op(op, left, right), false),
                Some(Expr::VarDecl { value, .. }) => {
                    if let Expr::Value(val) = &**value {
                        match val {
                            Value::Int(i) => {
                                if *is_negate_minus {
                                    (Value::Int(-i), false)
                                } else {
                                    (val.clone(), false)
                                }
                            }
                            Value::Float(f) => {
                                if *is_negate_minus {
                                    (Value::Float(-f), false)
                                } else {
                                    (val.clone(), false)
                                }
                            }
                            Value::Bool(b) => {
                                if *is_negate_not {
                                    (Value::Bool(!b), false)
                                } else {
                                    (val.clone(), false)
                                }
                            }
                            Value::Str(_) => (val.clone(), false),
                            Value::Null => (val.clone(), false),
                        }
                    } else {
                        eval_ast(parser, value)
                    }
                }
                Some(expr) => eval_ast(parser, expr),
                None => {
                    panic!("Variable '{}' not found in any scope", name)
                }
            }
        }
        Expr::Value(v) => (v.clone(), false),
        Expr::BinaryOp { op, left, right } => (parser.bin_op(op, left, right), false),
        Expr::PrintLn(expr) => {
            let result = eval_ast(parser, expr);
            match result.clone().0 {
                Value::Int(i) => parser.utils.write_to_cli(&format!("{:?}\n", i)),
                Value::Bool(b) => parser.utils.write_to_cli(&format!("{:?}\n", b)),
                Value::Str(s) => parser.utils.write_to_cli(&format!("{}\n", s)),
                Value::Null => parser.utils.write_to_cli(&format!("{:?}\n", result)),
                Value::Float(f) => parser.utils.write_to_cli(&format!("{:?}\n", f)),
            }
            result
            //self.eval_ast(expr)
        }
        Expr::PrintSingle(expr) => {
            let result = eval_ast(parser, expr);
            match result.clone().0 {
                Value::Int(i) => parser.utils.write_to_cli_single(&format!("{:?}\n", i)),
                Value::Bool(b) => parser.utils.write_to_cli_single(&format!("{:?}\n", b)),
                Value::Str(s) => parser.utils.write_to_cli_single(&format!("{}\n", s)),
                Value::Null => parser.utils.write_to_cli_single(&format!("{:?}\n", result)),
                Value::Float(f) => parser.utils.write_to_cli_single(&format!("{:?}\n", f)),
            }
            result
        }
        Expr::VarUpdate { .. } => {
            let val = eval_var_update(parser, expr);
            eval_ast(parser, &Expr::Value(val))
        }
        Expr::VarDecl {
            name,
            type_name: _,
            mutable: _,
            value,
        } => {
            if parser.variable_stack.contains_key(name) {
                panic!("Variable '{}' already in scope", name)
            }

            //parser.variable_stack.insert(name.to_string(), expr.clone());

            /*if let Expr::InputMacro = **value {
                eval_ast(parser, &Expr::Value(Value::Str("".to_owned())))
            } else {
                eval_ast(parser, value)
            }*/

            //eval_ast(parser, value)

            if let Expr::InputMacro = **value {
                let val = eval_ast(parser, value);
                parser
                    .variable_stack
                    .insert(name.to_string(), Expr::Value(val.0));

                (Value::Null, val.1)
            } else {
                parser.variable_stack.insert(name.to_string(), expr.clone());
                eval_ast(parser, value)
            }
        }
        Expr::FunctionDef {
            name,
            params,
            body,
            return_type,
        } => {
            let func = Function {
                params: params.clone(),
                body: *body.clone(),
                return_type: return_type.clone(),
            };
            parser.functions.insert(name.clone(), func);

            (Value::Null, false)
        }
        Expr::FunctionCall {
            name,
            args,
            is_negate_minus,
            is_negate_not,
        } => {
            if name == "main" {
                if !parser.main_called {
                    parser.main_called = true;
                } else {
                    panic!("Cannot call 'main()' as function call")
                }
            }
            let func = parser
                .functions
                .get(name)
                .unwrap_or_else(|| panic!("Function `{}` not found", name))
                .clone();

            if func.params.len() != args.len() {
                panic!(
                    "Function `{}` expected {} arguments, got {}",
                    name,
                    func.params.len(),
                    args.len()
                );
            }

            let old_vars = parser.variable_stack.clone();

            let mut temp_vars = HashMap::new();
            #[allow(unused_assignments)]
            for ((mutable, param_name, _), arg_expr) in func.params.iter().zip(args.iter()) {
                let val = eval_ast(parser, arg_expr);
                let mut type_name = String::new();
                match val.0 {
                    Value::Int(_) => type_name = "int".to_owned(),
                    Value::Bool(_) => type_name = "bool".to_owned(),
                    Value::Str(_) => type_name = "str".to_owned(),
                    Value::Null => type_name = "null".to_owned(),
                    Value::Float(_) => type_name = "float".to_owned(),
                }
                let var = Expr::VarDecl {
                    name: param_name.to_string(),
                    mutable: *mutable,
                    type_name,
                    value: Box::new(Expr::Value(val.0)),
                };
                temp_vars.insert(param_name, var);
            }
            parser.variable_stack.clear();
            for (param_name, var) in temp_vars {
                parser.variable_stack.insert(param_name.clone(), var);
            }

            parser.returned_if = false;

            parser.final_return = (Value::Null, false);
            #[allow(unused_assignments)]
            for expr in &func.body {
                if parser.returned_if {
                    return parser.final_return.clone();
                }
                match expr {
                    Expr::Return(inner_expr) => {
                        let mut val = eval_ast(parser, inner_expr);

                        let t = &parser.match_type(&Expr::Value(val.clone().0));
                        let s = parser.get_type_str(t).to_string();
                        let expected_type = &func.return_type;
                        let actual_type = parser.type_str_to_enum(s);

                        if *expected_type != Type::Null && expected_type != &actual_type {
                            panic!(
                                "Function `{}` should return `{:?}`, but returned `{:?}`",
                                name, expected_type, actual_type
                            );
                        }
                        if *expected_type == Type::Null {
                            panic!(
                                "Function `{}` should not return a value (Null), but returned `{:?}`",
                                name, actual_type
                            );
                        }

                        parser.variable_stack = old_vars;
                        match val.0 {
                            Value::Int(i2) => {
                                if *is_negate_minus {
                                    val = (Value::Int(-i2), true);
                                }
                            }
                            Value::Float(f2) => {
                                if *is_negate_minus {
                                    val = (Value::Float(-f2), true);
                                }
                            }
                            Value::Bool(b) => {
                                if *is_negate_not {
                                    val = (Value::Bool(!b), true);
                                }
                            }
                            _ => {}
                        }
                        parser.final_return = val.clone();
                        return val;
                    }
                    _ => {
                        let mut e = eval_ast(parser, expr);

                        if let Expr::If { .. } = expr {
                        } else {
                            parser.returned_if = false;
                            e.1 = false;
                        }

                        if e.1 {
                            let t = &parser.match_type(&Expr::Value(e.0.clone()));
                            let s = parser.get_type_str(t).to_string();
                            let expected_type = &func.return_type;
                            let actual_type = parser.type_str_to_enum(s);

                            if *expected_type != Type::Null && expected_type != &actual_type {
                                panic!(
                                    "Function `{}` should return `{:?}`, but returned `{:?}`",
                                    name, expected_type, actual_type
                                );
                            }

                            parser.variable_stack = old_vars;
                            match e.0 {
                                Value::Int(i2) => {
                                    if *is_negate_minus {
                                        e = (Value::Int(-i2), false);
                                    }
                                }
                                Value::Float(f2) => {
                                    if *is_negate_minus {
                                        e = (Value::Float(-f2), false);
                                    }
                                }
                                Value::Bool(b) => {
                                    if *is_negate_not {
                                        e = (Value::Bool(!b), false);
                                    }
                                }
                                _ => {}
                            }
                            parser.returned_if = true;
                            parser.final_return = e.clone();
                            return e;
                        }
                    }
                }
            }

            if func.return_type != Type::Null {
                panic!(
                    "Function `{}` declared to return `{:?}`, but no return statement was found",
                    name, func.return_type
                );
            }

            parser.variable_stack = old_vars;
            (Value::Null, false)
        }
        Expr::Return(expr) => eval_ast(parser, expr),
    };
    result
}
