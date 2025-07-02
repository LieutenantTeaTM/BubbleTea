use std::collections::HashSet;

use crate::{
    SymbolTable,
    general::ast::{Expr, ExternFunction, Type, Value},
};

pub struct Transpiler {
    pub e_funcs: Vec<ExternFunction>,
    pub transpiled_code: String,
}

impl Transpiler {
    pub fn new() -> Self {
        Transpiler {
            e_funcs: Vec::new(),
            transpiled_code: String::new(),
        }
    }

    pub fn load_extern_funcs(&mut self, extern_funcs: Vec<ExternFunction>) {
        let mut imported_files = HashSet::new();
        self.e_funcs = extern_funcs;
        for ext in self.e_funcs.clone() {
            if !imported_files.contains(&ext.file) {
                self.transpiled_code
                    .push_str(&format!("mod {};\n", ext.file.strip_suffix(".rs").unwrap()));
                imported_files.insert(ext.file.clone());
            }
            self.transpiled_code.push_str(&format!(
                "use {}::{};\n",
                ext.file.strip_suffix(".rs").unwrap(),
                ext.name
            ));
        }
    }

    fn transpile_value(
        &mut self,
        value: &Value,
        is_unary_not: bool,
        is_unary_minus: bool,
    ) -> String {
        match value {
            Value::Int(i) => {
                let mut i2 = i.to_string();
                if is_unary_minus {
                    i2 = format!("-{}", i2)
                }
                i2
            }
            Value::Float(f) => {
                if f.fract() == 0.0 {
                    let mut f2 = format!("{:.1}", f);
                    if is_unary_minus {
                        f2 = format!("-{}", f2)
                    }
                    f2
                } else {
                    let mut f2 = f.to_string();
                    if is_unary_minus {
                        f2 = format!("-{}", f2)
                    }
                    f2
                }
            }
            Value::Bool(b) => {
                let mut b2 = b.to_string();
                if is_unary_not {
                    b2 = format!("!{}", b2);
                }
                b2
            }
            Value::Str(s) => format!("\"{}\".to_string()", s),
            Value::Null => "None".to_string(),
        }
    }

    pub fn transpile_expr(
        &mut self,
        expr: &Expr,
        is_statement: bool,
        symbols: &mut SymbolTable,
    ) -> String {
        match expr {
            Expr::Return(val) => format!("return {};", self.transpile_expr(val, false, symbols)),
            Expr::Ident(name, _, _) => {
                if let Some(ty) = symbols.get(name) {
                    match ty {
                        Type::Str => format!("{}.to_string()", name),
                        _ => name.clone(),
                    }
                } else {
                    panic!("Ident not found in symbol table, cancelling transpile")
                }
            }
            Expr::Value {
                value,
                is_negate_not,
                is_negate_minus,
            } => self.transpile_value(value, *is_negate_not, *is_negate_minus),
            Expr::PrintLn(val) => format!(
                "println!(\"{{}}\", {});",
                self.transpile_expr(val, false, symbols)
            ),
            Expr::PrintSingle(val) => {
                format!(
                    "print!(\"{{}}\", {});",
                    self.transpile_expr(val, false, symbols)
                )
            }
            Expr::SuperPrint(val) => {
                let inner = self.transpile_expr(val, false, symbols);
                format!("println!(\"{{:?}}\", {});", inner)
            }
            Expr::InputMacro => "{
                let mut input = String::new();
                std::io::stdin().read_line(&mut input).unwrap();
                input.trim().to_string()
            }"
            .to_string(),
            Expr::Sleep(duration_expr) => format!(
                "std::thread::sleep(std::time::Duration::from_millis({} as u64));",
                self.transpile_expr(duration_expr, true, symbols)
            ),
            Expr::While { condition, body } => {
                let cond = self.transpile_expr(condition, true, symbols);
                let body_code = body
                    .iter()
                    .map(|e| self.transpile_expr(e, true, symbols))
                    .collect::<Vec<_>>()
                    .join("\n");
                format!("while {} {{\n{}\n}}", cond, body_code)
            }
            Expr::For {
                iter_start_name,
                to_iter_var,
                body,
            } => {
                let to_var = self.transpile_expr(to_iter_var, true, symbols);
                let body_code = body
                    .iter()
                    .map(|e| self.transpile_expr(e, true, symbols))
                    .collect::<Vec<_>>()
                    .join("\n");
                format!(
                    "for {} in 0..{} {{\n{}\n}}",
                    iter_start_name, to_var, body_code
                )
            }
            Expr::If {
                condition,
                body,
                else_branch,
            } => {
                let cond = self.transpile_expr(condition, true, symbols);
                let body_code = body
                    .iter()
                    .map(|e| self.transpile_expr(e, true, symbols))
                    .collect::<Vec<_>>()
                    .join("\n");
                let else_code = if let Some(else_branch) = else_branch {
                    format!("else {}", self.transpile_expr(else_branch, true, symbols))
                } else {
                    "".to_string()
                };
                format!("if {} {{\n{}\n}}{}", cond, body_code, else_code)
            }
            Expr::Else { body } => {
                let body_code = body
                    .iter()
                    .map(|e| self.transpile_expr(e, true, symbols))
                    .collect::<Vec<_>>()
                    .join("\n");
                format!("{{\n{}\n}}", body_code)
            }
            Expr::BinaryOp { op, left, right } => {
                let mut op2 = op.to_owned();
                if op2 == "::" {
                    op2 = "==".to_owned();
                } else if op2 == "!:" {
                    op2 = "!=".to_owned();
                } else if op2 == ">:" {
                    op2 = ">=".to_owned();
                } else if op2 == "<:" {
                    op2 = "<=".to_owned();
                }
                let l = self.transpile_expr(left, false, symbols);
                let mut r = self.transpile_expr(right, false, symbols);
                if l.ends_with(".to_string()") {
                    let res = r.strip_suffix(".to_string()");
                    if res.is_some() {
                        r = res.unwrap().to_string();
                        r.insert(0, '&');
                    }
                }
                format!("{} {} {}", l, op2, r)
            }
            Expr::VarUpdate { var, new_value } => {
                format!(
                    "{} = {};",
                    var.to_owned(),
                    self.transpile_expr(new_value, false, symbols)
                )
            }
            Expr::VarDecl {
                name,
                mutable,
                type_name,
                value,
            } => {
                let mut_keyword = if *mutable { "mut " } else { "" };
                let rust_type = transpile_type_name(type_name);
                let val_code = self.transpile_expr(value, false, symbols);
                symbols.insert(
                    name.clone(),
                    transpile_type_name_from_str(&type_name.clone()).clone(),
                );
                format!("let {mut_keyword}{name}: {rust_type} = {val_code};")
            }
            Expr::FunctionDef {
                name,
                params,
                body,
                return_type,
            } => {
                let mut local_symbols = SymbolTable::new();

                for (_, param_name, param_type) in params {
                    local_symbols.insert(param_name.clone(), param_type.clone());
                }

                let params_code = params
                    .iter()
                    .map(|(_, param_name, param_type)| {
                        format!("{}: {}", param_name, transpile_type(param_type))
                    })
                    .collect::<Vec<_>>()
                    .join(", ");
                let body_code = body
                    .iter()
                    .map(|e| self.transpile_expr(e, true, &mut local_symbols))
                    .collect::<Vec<_>>()
                    .join("\n");
                let ret_type = transpile_type(return_type);
                if ret_type == "()" {
                    format!("fn {}({}) {{\n{}\n}}", name, params_code, body_code)
                } else {
                    format!(
                        "fn {}({}) -> {} {{\n{}\n}}",
                        name, params_code, ret_type, body_code
                    )
                }
            }
            Expr::FunctionCall {
                name,
                args,
                is_negate_not,
                is_negate_minus,
            } => {
                let mut args_code = args
                    .iter()
                    .map(|e| self.transpile_expr(e, false, symbols))
                    .collect::<Vec<_>>()
                    .join(", ");
                if *is_negate_not {
                    args_code = format!("!({})", args_code);
                }
                if *is_negate_minus {
                    args_code = format!("-({})", args_code);
                }
                let call_code = format!("{}({})", name, args_code);

                if is_statement {
                    format!("{};", call_code)
                } else {
                    call_code
                }
            }
            Expr::CustomMacro { name, args } => {
                if self.e_funcs.iter().any(|f| f.name == *name) {
                    let args_code: Vec<_> = args
                        .iter()
                        .map(|arg| self.transpile_expr(arg, false, symbols))
                        .collect();
                    format!("{}({})", name, args_code.join(", "))
                } else {
                    panic!("Could not find custom macro '{}'", name)
                }
            }
            Expr::MacroDefine { .. } => String::new(),
        }
    }
}

fn transpile_type(t: &Type) -> &'static str {
    match t {
        Type::Int => "i64",
        Type::Float => "f64",
        Type::Bool => "bool",
        Type::Str => "String",
        Type::Null => "()",
    }
}

fn transpile_type_name(name: &str) -> &str {
    match name {
        "int" => "i64",
        "float" => "f64",
        "bool" => "bool",
        "str" => "String",
        "null" => "()",
        _ => "()", // fallback
    }
}

fn transpile_type_name_from_str(name: &str) -> &Type {
    match name {
        "int" => &Type::Int,
        "float" => &Type::Float,
        "bool" => &Type::Bool,
        "str" => &Type::Str,
        "null" => &Type::Null,
        _ => &Type::Null, // fallback
    }
}
