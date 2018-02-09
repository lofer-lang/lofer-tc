use eval::reduce;
use substitution::substitute;

#[derive(Clone, PartialEq, Debug)]
pub enum Expression {
    Variable(usize), // variables should be indexed from the end of the list?

    IntroPoint,

    IntroTT,
    IntroFF,
    ElimIf {
        condition: Box<Expression>,
        tt_branch: Box<Expression>,
        ff_branch: Box<Expression>,
        out_type: Box<Expression>,
    },

    IntroLambda {
        in_type: Box<Expression>,
        body: Box<Expression>,
    },
    ElimApplication {
        function: Box<Expression>,
        argument: Box<Expression>,
    },

    IntroPair {
        fst: Box<Expression>,
        snd: Box<Expression>,
        snd_type: Box<Expression>,
    },
    ElimFst {
        pair: Box<Expression>,
    },
    ElimSnd {
        pair: Box<Expression>,
    },

    IntroType(Box<Type>),
    // type eliminator one day :o
}

impl Expression {
    pub fn substitute(self: &Self, var: &Self) -> Self {
        substitute(self, 0, var)
    }

    pub fn reduce(self: &Self) -> Self {
        reduce(self)
    }
}

#[derive(Clone, PartialEq, Debug)]
pub enum Type {
    Void,
    Unit,
    Bool,
    Pi {
        domain: Box<Expression>,
        codomain: Box<Expression>,
    },
    Sigma {
        fst_type: Box<Expression>,
        snd_type: Box<Expression>,
    },
    Universe/*(usize)*/,
}

pub fn var(n: usize) -> Expression {
    Expression::Variable(n)
}

pub fn point() -> Expression {
    Expression::IntroPoint
}

pub fn tt() -> Expression {
    Expression::IntroTT
}

pub fn ff() -> Expression {
    Expression::IntroFF
}

// would make a version with inference, but passing the context in is less
// intuitive than passing the actual type in
pub fn if_then_else(
    condition: Expression,
    tt_branch: Expression,
    ff_branch: Expression,
    out_type: Expression,
) -> Expression {
    let condition = Box::new(condition);
    let tt_branch = Box::new(tt_branch);
    let ff_branch = Box::new(ff_branch);
    let out_type = Box::new(out_type);
    Expression::ElimIf { condition, tt_branch, ff_branch, out_type }
}

pub fn lambda(in_type: Expression, body: Expression)
    -> Expression
{
    let in_type = Box::new(in_type);
    let body = Box::new(body);
    Expression::IntroLambda { in_type, body }
}

pub fn apply(function: Expression, argument: Expression) -> Expression {
    let function = Box::new(function);
    let argument = Box::new(argument);
    Expression::ElimApplication { function, argument }
}

// see if-then-else on the subject of type inference
pub fn pair(fst: Expression, snd: Expression, snd_type: Expression) -> Expression {
    let fst = Box::new(fst);
    let snd = Box::new(snd);
    let snd_type = Box::new(snd_type);
    Expression::IntroPair { fst, snd, snd_type }
}

pub fn fst(pair: Expression) -> Expression {
    let pair = Box::new(pair);
    Expression::ElimFst { pair }
}

pub fn snd(pair: Expression) -> Expression {
    let pair = Box::new(pair);
    Expression::ElimSnd { pair }
}

pub fn simple_type(typ: Type) -> Expression {
    let typ = Box::new(typ);
    Expression::IntroType(typ)
}

pub fn void() -> Expression {
    simple_type(Type::Void)
}

pub fn unit() -> Expression {
    simple_type(Type::Unit)
}

pub fn bool() -> Expression {
    simple_type(Type::Bool)
}

pub fn pi(domain: Expression, codomain: Expression) -> Expression {
    let domain = Box::new(domain);
    let codomain = Box::new(codomain);
    let out = Type::Pi { domain, codomain };
    simple_type(out)
}

pub fn sigma(fst_type: Expression, snd_type: Expression) -> Expression {
    let fst_type = Box::new(fst_type);
    let snd_type = Box::new(snd_type);
    let out = Type::Sigma { fst_type, snd_type };
    simple_type(out)
}

pub fn universe() -> Expression {
    simple_type(Type::Universe)
}

