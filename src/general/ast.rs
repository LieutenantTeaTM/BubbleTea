#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    Int(i64),
    Float(f64),
    Bool(bool),
    Str(String),
    Null,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExternFunction {
    pub name: String,
    pub file: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Type {
    Int,
    Float,
    Bool,
    Str,
    Null,
}

#[derive(Debug, Clone, PartialEq)]
#[allow(dead_code)]
pub enum Expr {
    Return(Box<Expr>),
    Ident(String, bool, bool),
    Value {
        value: Value,
        is_negate_not: bool,
        is_negate_minus: bool,
    },
    PrintLn(Box<Expr>),
    PrintSingle(Box<Expr>),
    SuperPrint(Box<Expr>),
    InputMacro,
    Sleep(Box<Expr>),
    While {
        condition: Box<Expr>,
        body: Vec<Expr>,
    },
    For {
        iter_start_name: String,
        to_iter_var: Box<Expr>,
        body: Vec<Expr>,
    },
    If {
        condition: Box<Expr>,
        body: Vec<Expr>,
        else_branch: Option<Box<Expr>>, // This can be another If or Else block
    },
    Else {
        body: Vec<Expr>,
    },
    BinaryOp {
        op: String,
        left: Box<Expr>,
        right: Box<Expr>,
    },
    VarUpdate {
        var: String,
        new_value: Box<Expr>,
    },
    VarDecl {
        name: String,
        mutable: bool,
        type_name: String,
        value: Box<Expr>,
    },
    #[allow(clippy::box_collection)]
    FunctionDef {
        name: String,
        params: Vec<(bool, String, Type)>,
        body: Box<Vec<Expr>>,
        return_type: Type,
    },
    FunctionCall {
        name: String,
        args: Vec<Expr>,
        is_negate_not: bool,
        is_negate_minus: bool,
    },
    CustomMacro {
        name: String,
        args: Vec<Expr>,
    },
    MacroDefine {
        func: ExternFunction,
    },
}
