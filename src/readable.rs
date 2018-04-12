
pub struct Program {
    pub output: Function,
    pub associated: Vec<Program>,
}

pub struct Function {
    pub fname: String,
    pub vars: Vec<Var>,
    pub body: Expression,
}

pub struct Var {
    pub name: String,
    pub typ: Expression,
}

pub struct Expression {
    pub head: HeadExpression,
    pub tail: Vec<Expression>,
}

pub enum HeadExpression {
    Name(String),
}


