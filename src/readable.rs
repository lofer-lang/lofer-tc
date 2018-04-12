
pub struct Program {
    output: Function,
    associated: Vec<Program>,
}

pub struct Function {
    fname: String,
    vars: Vec<Var>,
    body: Expression,
}

pub struct Var {
    name: String,
    typ: Expression,
}

pub struct Expression {
    head: HeadExpression,
    tail: Vec<Expression>,
}

pub enum HeadExpression {
    Name(String),
}


