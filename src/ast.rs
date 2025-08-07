use std::{
    collections::HashMap,
    fmt::{Binary, Display},
};

use crate::{js_backend::ToJS, lexer::Literal, symbol_table::SymbolTable, FStringPart};

#[derive(Debug, Copy, Clone, PartialEq)]
pub enum UnaryOperation {
    Negative,
    Negate,
    Reference,
    Pointer,
    Dereference,
}

impl Display for UnaryOperation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let str = match self {
            UnaryOperation::Negative => "-",
            UnaryOperation::Negate => "!",
            UnaryOperation::Reference => "&",
            UnaryOperation::Pointer => "^",
            UnaryOperation::Dereference => "^",
        };

        f.write_str(str)
    }
}

#[derive(Debug, Copy, Clone, PartialEq)]
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

impl Display for BinaryOperation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let str = match self {
            BinaryOperation::Add => "+",
            BinaryOperation::Subtract => "-",
            BinaryOperation::Multiply => "*",
            BinaryOperation::Divide => "/",
            BinaryOperation::Power => "^",
            BinaryOperation::And => "&&",
            BinaryOperation::Or => "||",
            BinaryOperation::Less => "<",
            BinaryOperation::LessEqual => "<=",
            BinaryOperation::Greater => ">",
            BinaryOperation::GreaterEqual => ">=",
            BinaryOperation::Equal => "==",
            BinaryOperation::NotEqual => "!=",
        };

        f.write_str(str)
    }
}

pub type SymbolIdx = (usize, usize); // scope idx, symbol idx

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunctionType {
    pub env_args: Vec<Type>,
    pub args: Vec<Type>,
    pub ret: Box<Type>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CustomType {
    pub name: String,
}

#[derive(Debug, Clone, Eq)]
pub enum Type {
    Infer,
    Any,
    Void,
    Int,
    Uint,
    Float,
    String,
    Boolean,
    Custom(CustomType),
    Array(Box<Type>),
    Function(FunctionType),
    Struct(StructDef),
    Reference(Box<Type>),
    Pointer(Box<Type>),
    Structural(Box<Type>),
}

impl Type {
    pub fn size(&self) -> usize {
        use Type::*;
        match self {
            Int => 8,
            Uint => 8,
            Float => 4,
            String => 8,
            Boolean => 8,
            Void => 0,
            Any => unimplemented!(),
            Array(_) => 8,
            Function(_) => unimplemented!(),
            Struct(_) => unimplemented!(),
            Reference(_) => 8,
            Pointer(_) => 8,
            Structural(_) => unimplemented!(),
            Infer => unimplemented!(),
            Custom(_) => unimplemented!(),
        }
    }
}

impl Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Custom(CustomType { name, .. }) => f.write_fmt(format_args!("{name}")),
            Self::Array(inner) => f.write_fmt(format_args!("[{inner}]")),
            Self::Function(FunctionType {
                env_args,
                args,
                ret,
            }) => {
                let args: Vec<_> = args.iter().map(|t| format!("{t}")).collect();
                let args = args.join(", ");

                f.write_fmt(format_args!("fn({args}) -> {ret}"))
            }
            Self::Struct(StructDef { fields }) => {
                let fields: Vec<_> = fields
                    .iter()
                    .map(|field| format!("{}: {}", field.field_name, field.field_type))
                    .collect();

                let fields = fields.join(", ");

                f.write_fmt(format_args!("{{ {fields} }}"))
            }
            Self::Reference(inner) => f.write_fmt(format_args!("&{inner}")),
            Self::Pointer(inner) => f.write_fmt(format_args!("^{inner}")),
            Self::Structural(inner) => f.write_fmt(format_args!("~{inner}")),
            other => f.write_str(&format!("{other:?}").to_lowercase()),
        }
    }
}

impl PartialEq for Type {
    fn eq(&self, other: &Self) -> bool {
        if matches!(self, Type::Any) || matches!(other, Type::Any) {
            return true;
        }

        if let Self::Struct(StructDef {
            fields: self_fields,
        }) = self
        {
            if let Self::Struct(StructDef {
                fields: other_fields,
            }) = other
            {
                for field in self_fields {
                    if !other_fields.contains(&field) {
                        return false;
                    }
                }

                return true;
            }
        }

        match (self, other) {
            (Type::Infer, Type::Infer)
            | (Type::Void, Type::Void)
            | (Type::Int, Type::Int)
            | (Type::Uint, Type::Uint)
            | (Type::Float, Type::Float)
            | (Type::String, Type::String)
            | (Type::Boolean, Type::Boolean) => return true,
            (Type::Custom(a), Type::Custom(b)) => return a == b,
            (Type::Array(a), Type::Array(b)) => return a == b,
            (Type::Function(a), Type::Function(b)) => return a == b,
            (Type::Reference(a), Type::Reference(b)) => return a == b,
            (Type::Pointer(a), Type::Pointer(b)) => return a == b,
            (Type::Structural(a), Type::Structural(b)) => return a == b,
            _ => return false,
        };
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct VariableDecl {
    pub var_name: String,
    pub var_type: Type,
    pub var_value: Box<Expression>,
    pub symbol_idx: SymbolIdx,
    pub byte_idx: usize, // at which byte does this decl start. used for shadowing
    pub is_mutable: bool,
    pub is_env: bool,
}

impl ToJS for VariableDecl {
    fn to_js(&self, st: &SymbolTable) -> String {
        let VariableDecl {
            var_name,
            var_type,
            var_value,
            byte_idx,
            is_mutable,
            symbol_idx,
            is_env,
        } = self;
        let var_name = var_name.replace("::", "_");
        let keyword = if *is_mutable { "let" } else { "const" };
        let value = var_value.to_js(st);

        format!("{keyword} {var_name} = {value};")
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct FunctionCall {
    pub func_expr: Box<Expression>,
    pub arguments: Vec<Expression>,
}

impl ToJS for FunctionCall {
    fn to_js(&self, st: &SymbolTable) -> String {
        let FunctionCall {
            func_expr,
            arguments,
        } = self;

        let func_expr = match func_expr.as_ref() {
            Expression::Variable(Variable { name, .. }) => name.replace("::", "_"),
            expr => expr.to_js(st),
        };

        let args = arguments
            .into_iter()
            .map(|arg| arg.to_js(st))
            .collect::<Vec<_>>()
            .join(", ");

        format!("{func_expr}({args})")
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct UnaryOp {
    pub op: UnaryOperation,
    pub operand: Box<Expression>,
}

impl ToJS for UnaryOp {
    fn to_js(&self, st: &SymbolTable) -> String {
        let UnaryOp { op, operand } = self;

        let op = match op {
            // TODO
            UnaryOperation::Pointer => "".to_owned(),
            UnaryOperation::Reference => "".to_owned(),
            UnaryOperation::Dereference => "".to_owned(),
            UnaryOperation::Negative => "-".to_owned(),
            UnaryOperation::Negate => "!".to_owned(),
        };

        let expr = operand.to_js(st);

        format!("({op}{expr})")
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct BinaryOp {
    pub op: BinaryOperation,
    pub lhs: Box<Expression>,
    pub rhs: Box<Expression>,
}

impl ToJS for BinaryOp {
    fn to_js(&self, st: &SymbolTable) -> String {
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

        let lhs = lhs.to_js(st);
        let rhs = rhs.to_js(st);

        format!("({lhs} {op} {rhs})")
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Variable {
    pub name: String,
    pub decl_scope: usize,
    pub symbol_idx: SymbolIdx,
}

impl ToJS for Variable {
    fn to_js(&self, st: &SymbolTable) -> String {
        let Variable { name, .. } = self;
        self.name.replace("::", "_")
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Assignment {
    pub lhs: Box<Expression>,
    pub rhs: Box<Expression>,
}

impl ToJS for Assignment {
    fn to_js(&self, st: &SymbolTable) -> String {
        let Assignment { lhs, rhs } = self;

        let lhs = lhs.to_js(st);
        let rhs = rhs.to_js(st);

        format!("{lhs} = {rhs}")
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct If {
    pub cond: Box<Expression>,
    pub true_branch: CodeBlock,
    pub else_branch: Option<CodeBlock>,
}

impl ToJS for If {
    fn to_js(&self, st: &SymbolTable) -> String {
        let If {
            cond,
            true_branch,
            else_branch,
        } = self;
        let cond = cond.to_js(st);
        let true_branch = true_branch.to_js(st);

        let else_branch = else_branch.clone().map_or(String::new(), |b| {
            let branch = b.to_js(st);
            format!(" else {{ {branch} }}")
        });

        format!("if ({cond}) {{ {true_branch} }}{else_branch}")
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct For {
    pub binding: String,
    pub symbol_idx: SymbolIdx,
    pub binding_type: Type,
    pub iterator: Box<Expression>,
    pub body: CodeBlock,
}

impl ToJS for For {
    fn to_js(&self, st: &SymbolTable) -> String {
        let For {
            binding,
            binding_type,
            symbol_idx,
            iterator,
            body,
        } = self;

        let iterator = iterator.to_js(st);
        let body = body.to_js(st);
        let binding = binding.replace("::", "_");

        format!("for (const {binding} of {iterator}) {{ {body} }}")
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct ArrayAccess {
    pub expr: Box<Expression>,
    pub index: Box<Expression>,
}

impl ToJS for ArrayAccess {
    fn to_js(&self, st: &SymbolTable) -> String {
        let ArrayAccess { expr, index } = self;

        let expr = expr.to_js(st);
        let index = index.to_js(st);

        format!("{expr}[{index}]")
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct ArrayLiteral {
    pub elements: Vec<Expression>,
}

impl ToJS for ArrayLiteral {
    fn to_js(&self, st: &SymbolTable) -> String {
        let elements = self
            .elements
            .iter()
            .map(|elem| elem.to_js(st))
            .collect::<Vec<_>>()
            .join(", ");

        format!("[ {elements} ]")
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct NamedStruct {
    pub casted_to: String,
    pub struct_literal: AnonStruct,
}

impl ToJS for NamedStruct {
    fn to_js(&self, st: &SymbolTable) -> String {
        let NamedStruct {
            casted_to,
            struct_literal,
        } = self;
        let struct_expr = struct_literal.to_js(st);

        format!("{struct_expr}")
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct AnonStruct {
    pub fields: HashMap<String, Expression>,
}

impl ToJS for AnonStruct {
    fn to_js(&self, st: &SymbolTable) -> String {
        let AnonStruct { fields } = self;

        let fields = fields
            .into_iter()
            .map(|(field_name, field_val)| {
                let val_expr = field_val.to_js(st);
                format!("{field_name}: {val_expr}")
            })
            .collect::<Vec<_>>()
            .join(", ");

        format!("{{ {fields} }}")
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Range {
    pub start: Box<Expression>,
    pub end: Box<Expression>,
    pub inclusive: bool,
}

impl ToJS for Range {
    fn to_js(&self, st: &SymbolTable) -> String {
        let Range {
            start,
            end,
            inclusive,
        } = self;

        unimplemented!("ranges arent directly transpilable");

        // format!("{{ {fields} }}")
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct FieldAccess {
    pub expr: Box<Expression>,
    pub field: String,
}

impl ToJS for FieldAccess {
    fn to_js(&self, st: &SymbolTable) -> String {
        let FieldAccess { expr, field } = self;

        let expr = expr.to_js(st);

        format!("{expr}.{field}")
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Lambda {
    pub argument_list: Vec<FunctionArgument>,
    pub return_type: Type,
    pub function_body: CodeBlock,
}

impl ToJS for Lambda {
    fn to_js(&self, st: &SymbolTable) -> String {
        let Lambda {
            argument_list,
            return_type,
            function_body,
        } = self;

        let args = argument_list
            .into_iter()
            .map(|arg| arg.arg_name.replace("::", "_"))
            .collect::<Vec<_>>()
            .join(", ");

        let body = function_body.to_js(st);

        format!("({args}) => {{ {body} }}\n")
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Expression {
    VariableDecl(VariableDecl),
    Literal(Literal),
    BinaryOp(BinaryOp),
    UnaryOp(UnaryOp),
    FunctionCall(FunctionCall),
    Variable(Variable),
    Return(Box<Expression>),
    Assignment(Assignment),
    AnonStruct(AnonStruct),
    ArrayLiteral(ArrayLiteral),
    ArrayAccess(ArrayAccess),
    FieldAccess(FieldAccess),
    NamedStruct(NamedStruct),
    Lambda(Lambda),
    Range(Range),
    BuiltinTarget(Box<Expression>),
    BuiltinType(Box<Expression>),
    If(If),
    For(For),
    Import(Import),
    Placeholder,
    Break,
    Continue,
}

impl ToJS for Expression {
    fn to_js(&self, st: &SymbolTable) -> String {
        match self {
            Self::VariableDecl(var_decl) => var_decl.to_js(st),
            Self::If(if_expr) => if_expr.to_js(st),
            Self::BinaryOp(bin_op) => bin_op.to_js(st),
            Self::UnaryOp(unary_op) => unary_op.to_js(st),
            Self::FunctionCall(func_call) => func_call.to_js(st),
            Self::Variable(var) => var.to_js(st),
            Self::Assignment(assignment) => assignment.to_js(st),
            Self::AnonStruct(struct_literal) => struct_literal.to_js(st),
            Self::ArrayLiteral(array_literal) => array_literal.to_js(st),
            Self::Lambda(lambda) => lambda.to_js(st),
            Self::ArrayAccess(array_access) => array_access.to_js(st),
            Self::FieldAccess(field_access) => field_access.to_js(st),
            Self::NamedStruct(cast_literal) => cast_literal.to_js(st),
            Self::Range(range) => range.to_js(st),
            Self::For(for_expr) => for_expr.to_js(st),
            Self::Return(expr) => {
                let expr = expr.to_js(st);
                format!("return ({expr});")
            }
            Self::Break => {
                format!("break;")
            }
            Self::Continue => {
                format!("continue;")
            }
            Self::Placeholder => {
                format!("{{ /* placeholder */ }}")
            }
            Self::Literal(literal) => match literal {
                Literal::Boolean(val) => format!("{val}"),
                Literal::Int(val) => format!("{val}"),
                Literal::Float(val) => format!("{val}"),
                Literal::Uint(val) => format!("{val}"),
                Literal::String(parts) => {
                    let mut str = "`".to_string();
                    for part in parts {
                        match part {
                            FStringPart::String(string) => str += string,
                            FStringPart::Code(expr) => str += &format!("${{{}}}", expr.to_js(st)),
                        }
                    }

                    str += "`";

                    str
                }
            },
            Self::Import(import) => format!("/* imported module {import:#?} */",),
            Self::BuiltinTarget(code) => {
                if let Expression::Literal(Literal::String(parts)) = code.as_ref() {
                    let mut js = "".to_string();
                    for part in parts {
                        let text = match part {
                            // TODO: this doesnt work if expr is an if or a for since js doesnt support that
                            FStringPart::Code(expr) => format!("({})", expr.to_js(st)),
                            FStringPart::String(string) => string.clone().replace("\\", ""),
                        };
                        js += &text;
                    }

                    return js;
                }

                unreachable!()
            }
            Self::BuiltinType(_) => unreachable!(), // kind => {
                                                    //     dbg!(kind);
                                                    //     unimplemented!("transpilation unimplemented")
                                                    // }
        }
    }
}

#[derive(Debug, Clone, Default, PartialEq)]
pub struct CodeBlock {
    pub indentation: usize,
    pub expressions: Vec<Expression>,
}

impl ToJS for CodeBlock {
    fn to_js(&self, st: &SymbolTable) -> String {
        let indentation = " ".repeat(self.indentation);

        let expressions = self
            .expressions
            .iter()
            .map(|expr| {
                let expr = expr.to_js(st);
                format!("{indentation}{expr}")
            })
            .collect::<Vec<_>>()
            .join("\n");

        format!("\n{expressions}")
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct FunctionArgument {
    pub arg_name: String,
    pub arg_type: Type,
    pub is_env: bool,
    pub symbol_idx: SymbolIdx,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Import {
    pub name: String,
    pub children: Vec<Import>,
    pub alias: Option<String>,
}

#[derive(Debug, Clone)]
pub struct FunctionDef {
    pub export: bool,
    pub func_name: String,
    pub argument_list: Vec<FunctionArgument>,
    pub return_type: Type,
    pub function_body: CodeBlock,
    pub symbol_idx: SymbolIdx,
}

impl ToJS for FunctionDef {
    fn to_js(&self, st: &SymbolTable) -> String {
        let FunctionDef {
            export,
            func_name,
            argument_list,
            return_type,
            symbol_idx,
            function_body,
        } = self;

        // let export = if *export { "export " } else { "" };
        let func_name = func_name.replace("::", "_");

        let args = argument_list
            .into_iter()
            .map(|arg| arg.arg_name.replace("::", "_"))
            .collect::<Vec<_>>()
            .join(", ");

        let body = function_body.to_js(st);

        format!("function {func_name}({args}) {{ {body} }}\n")
    }
}

#[derive(Debug, Clone)]
pub struct VariantDef {
    pub variant_name: String,
    pub fields: Vec<StructField>,
}

#[derive(Debug, Clone)]
pub struct EnumDef {
    pub enum_name: String,
    pub variants: Vec<VariantDef>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StructField {
    pub field_name: String,
    pub field_type: Type,
    pub is_final: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StructDef {
    pub fields: Vec<StructField>,
}

#[derive(Debug, Clone)]
pub struct TypeDef {
    pub name: String,
    pub export: bool,
    pub underlying_ty: Type,
    pub symbol_idx: SymbolIdx,
}

#[derive(Debug, Clone, Default)]
pub struct Module {
    pub module_name: String,
    pub type_defs: Vec<TypeDef>,
    pub function_defs: Vec<FunctionDef>,
    pub toplevel_scope: CodeBlock,
    pub reachable_modules: Vec<String>,
}
