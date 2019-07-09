#[derive(Clone)]
pub enum Expr {
    Arrow(ArrowExpr),
    Alg(AlgExpr),
}

#[derive(Clone)]
pub struct ArrowExpr {
    pub params: Vec<(Option<String>, Expr)>,
    pub output: Box<Expr>,
}

#[derive(Clone)]
pub struct AlgExpr {
    pub head: String,
    pub tail: Vec<Expr>,
}

pub struct Function {
    pub fname: String,
    pub vars: Vec<String>,
    pub body: Expr,
}

pub struct Annotation {
    pub name: String,
    pub typ: Expr,
}

pub enum Line {
    Annotation(Annotation),
    Function(Function),
}

pub struct Item {
    pub annotation: Option<Annotation>,
    pub definition: Function,
    pub associated: Vec<Item>,
}
