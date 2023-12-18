use std::{collections::HashMap, fmt::Binary};

use crate::{lexer::Literal, transpiler::ToJS};


#[derive(Debug, Clone)]
pub enum BinaryOperation {
    Add,
    Subtract,
    Multiply,
    Divide,
    Power,
    And,
    Or,
    Less,
    LessEqual,
    Greater,
    GreaterEqual,
    Equal,
    NotEqual,
}

#[derive(Debug, Clone)]
pub enum TypeKind {
    Infer, 
    Void,
    Int,
    Uint,
    Float,
    String,
    Boolean,
    Custom(String),
}

#[derive(Debug, Clone)]
pub struct Type {
    pub type_kind: TypeKind,
    pub is_reference: bool,
}


#[derive(Debug, Clone)]
pub struct VariableDecl  {
    pub var_name: String,
    pub var_type: Type,
    pub var_value: Box<Expression>,
    pub is_mutable: bool,
    pub is_implicit: bool,
}

impl ToJS for VariableDecl {
    fn to_js(&self) -> String {
        let VariableDecl { var_name, var_type, var_value, is_mutable, is_implicit } = self;
        let keyword = if *is_mutable { "let" } else { "const" };
        let value = var_value.to_js();

        format!("{keyword} {var_name} = {value};")
    }
}

#[derive(Debug, Clone)]
pub struct FunctionCall  {
    pub func_name: String,
    pub arguments: Vec<Expression>,
}

impl ToJS for FunctionCall {
    fn to_js(&self) -> String {
        let FunctionCall { func_name, arguments } = self;

        let args = arguments
            .into_iter()
            .map(|arg| {
                arg.to_js()
            })
            .collect::<Vec<_>>()
            .join(", ");

        format!("{func_name}({args})")
    }
}

#[derive(Debug, Clone)]
pub struct BinaryOp  {
    pub op: BinaryOperation,
    pub lhs: Box<Expression>,
    pub rhs: Box<Expression>,
}

impl ToJS for BinaryOp {
    fn to_js(&self) -> String {
        let BinaryOp { op, lhs, rhs } = self;

        let op = match op {
            BinaryOperation::Add => "+".to_owned(),
            BinaryOperation::Subtract => "-".to_owned(),
            BinaryOperation::Multiply => "*".to_owned(),
            BinaryOperation::Divide => "/".to_owned(),
            BinaryOperation::Less => "<".to_owned(),
            BinaryOperation::LessEqual => "<=".to_owned(),
            BinaryOperation::Greater => ">".to_owned(),
            BinaryOperation::GreaterEqual => ">=".to_owned(),
            BinaryOperation::NotEqual => "!=".to_owned(),
            BinaryOperation::Equal => "==".to_owned(),
            BinaryOperation::Power => "^".to_owned(),
            BinaryOperation::And => "&&".to_owned(),
            BinaryOperation::Or => "||".to_owned(),
        };

        let lhs = lhs.to_js();
        let rhs = rhs.to_js();

        format!("({lhs} {op} {rhs})")
    }
}

#[derive(Debug, Clone)]
pub struct Variable  {
    pub name: String,
}

impl ToJS for Variable {
    fn to_js(&self) -> String {
       self.name.clone()
    }
}

#[derive(Debug, Clone)]
pub struct Assignment  {
    pub lhs: String,
    pub rhs: Box<Expression>,
}

impl ToJS for Assignment {
    fn to_js(&self) -> String {
        let Assignment { lhs, rhs } = self;
        
        let rhs = rhs.to_js();

        format!("{lhs} = {rhs}")
    }
}

#[derive(Debug, Clone)]
pub struct If  {
    pub cond: Box<Expression>,
    pub true_branch: CodeBlock,
    pub else_branch: Option<CodeBlock>,
}

impl ToJS for If {
    fn to_js(&self) -> String {
        let If { cond, true_branch, else_branch } = self;
        let cond = cond.to_js();
        let true_branch = true_branch.to_js();

        let else_branch = else_branch
            .clone()
            .map_or(String::new(), |b| {
                let branch = b.to_js();
                format!(" else {{ {branch} }}")
            });

        format!("if ({cond}) {{ {true_branch} }}{else_branch}")
    }
}

#[derive(Debug, Clone)]
pub struct For  {
    pub binding: String,
    pub iterator: Box<Expression>,
    pub body: CodeBlock,
}

impl ToJS for For {
    fn to_js(&self) -> String {
        let For { binding, iterator, body } = self;

        let iterator = iterator.to_js();
        let body = body.to_js();

        format!("for (const {binding} of {iterator}) {{ {body} }}")
    }
}

#[derive(Debug, Clone)]
pub struct ArrayAccess  {
    pub expr: Box<Expression>,
    pub index: Box<Expression>,
}

impl ToJS for ArrayAccess {
    fn to_js(&self) -> String {
        let ArrayAccess { expr, index } = self;

        let expr = expr.to_js();
        let index = index.to_js();

        format!("{expr}[{index}]")
    }
}

#[derive(Debug, Clone)]
pub struct ArrayLiteral  {
    pub elements: Vec<Expression>,
}

impl ToJS for ArrayLiteral {
    fn to_js(&self) -> String {
        let elements = self.elements
            .iter()
            .map(|elem| {
                elem.to_js()
            })
            .collect::<Vec<_>>()
            .join(", ");

        format!("[ {elements} ]")
    }
}

#[derive(Debug, Clone)]
pub struct StructLiteral  {
    pub name: String,
    pub fields: HashMap<String, Expression>,
}

impl ToJS for StructLiteral {
    fn to_js(&self) -> String {
        let StructLiteral { name, fields } = self;

        let fields = fields
            .into_iter()
            .map(|(field_name, field_val)| {
                let val_expr = field_val.to_js();
                format!("{field_name}: {val_expr}")
            })
            .collect::<Vec<_>>()
            .join(", ");

        format!("{{ {fields} }}")
    }
}

#[derive(Debug, Clone)]
pub enum Expression {
    VariableDecl(VariableDecl),
    Literal(Literal),
    BinaryOp(BinaryOp),
    FunctionCall(FunctionCall),
    Variable(Variable),
    Return(Box<Expression>),
    Assignment(Assignment),
    StructLiteral(StructLiteral),
    ArrayLiteral(ArrayLiteral),
    ArrayAccess(ArrayAccess),
    JS(String),
    If(If),
    For(For),
    Placeholder,
    Break,
    Continue
}

impl ToJS for Expression {
    fn to_js(&self) -> String {
        match self {
            Self::VariableDecl(var_decl) => var_decl.to_js(),
            Self::If(if_expr) => if_expr.to_js(),
            Self::BinaryOp(bin_op) => bin_op.to_js(),
            Self::FunctionCall(func_call) => func_call.to_js(),
            Self::Variable(var) => var.to_js(),
            Self::Assignment(assignment) => assignment.to_js(),
            Self::StructLiteral(struct_literal) => struct_literal.to_js(),
            Self::ArrayLiteral(array_literal) => array_literal.to_js(),
            Self::ArrayAccess(array_access) => array_access.to_js(),
            Self::For(for_expr) => for_expr.to_js(),
            Self::Return(expr) => {
                let expr = expr.to_js();
                format!("return ({expr});")
            }
            Self::Break => {
                format!("break;")
            }
            Self::Continue => {
                format!("continue;")
            }
            Self::Placeholder => {
                eprintln!("Transpiling placeholder");
                format!("{{ /* placeholder */ }}")
            }
            Self::Literal(literal) => {
                match literal {
                    Literal::Boolean(val) => format!("{val}"),
                    Literal::Int(val) => format!("{val}"),
                    Literal::Float(val) => format!("{val}"),
                    Literal::Uint(val) => format!("{val}"),
                    Literal::String(val) => format!("{val:?}"),
                }
            },
            Self::JS(code) => {
                format!("{code}")
            }
            // kind => {
            //     dbg!(kind);
            //     unimplemented!("transpilation unimplemented")
            // }
        }
    }
}

#[derive(Debug, Clone, Default)]
pub struct CodeBlock  {
    pub indentation: usize,
    pub expressions: Vec<Expression>
}

impl ToJS for CodeBlock {
    fn to_js(&self) -> String {
        let indentation = " ".repeat(self.indentation);

        let expressions = self.expressions
            .iter()
            .map(|expr| {
                let expr = expr.to_js();
                format!("{indentation}{expr}")
            })
            .collect::<Vec<_>>()
            .join("\n");

        format!("\n{expressions}")
    }
}

#[derive(Debug, Clone)]
pub struct FunctionArgument {
    pub arg_name: String,
    pub arg_type: Type,
    pub is_implicit: bool,
}

#[derive(Debug, Clone)]
pub struct FunctionDef {
    pub export: bool,
    pub func_name: String,
    pub argument_list: Vec<FunctionArgument>,
    pub return_type: Type,
    pub function_body: CodeBlock
}

impl ToJS for FunctionDef {
    fn to_js(&self) -> String {
        let FunctionDef { export, func_name, argument_list, return_type, function_body } = self;

        let export = if *export { "export " } else { "" };

        let args = argument_list
            .into_iter()
            .map(|arg| {
                arg.arg_name.clone()
            })
            .collect::<Vec<_>>()
            .join(", ");

        let body = function_body.to_js();
        
        format!("{export}function {func_name}({args}) {{ {body} }};\n")
    }
}

#[derive(Debug, Clone)]
pub struct VariantDef {
    pub variant_name: String,
    pub fields: Vec<StructField>
}

#[derive(Debug, Clone)]
pub struct EnumDef {
    pub enum_name: String,
    pub variants: Vec<VariantDef>
}

#[derive(Debug, Clone)]
pub struct StructField {
    pub field_name: String,
    pub field_type: Type,
    pub is_final: bool,
    pub default_value: Box<Expression>
}

#[derive(Debug, Clone)]
pub struct StructDef {
    pub struct_name: String,
    pub fields: Vec<StructField>,
    pub methods: Vec<FunctionDef> 
}

#[derive(Debug, Clone)]
pub struct TypeDef {
    pub export: bool,
    pub type_kind: TypeDefKind
}

#[derive(Debug, Clone)]
pub enum TypeDefKind {
    EnumDef(EnumDef),
    StructDef(StructDef)
}

#[derive(Debug, Clone, Default)]
pub struct Module {
    pub module_name: String,
    pub type_defs: Vec<TypeDef>,
    pub function_defs: Vec<FunctionDef>,
    pub toplevel_scope: CodeBlock
}

