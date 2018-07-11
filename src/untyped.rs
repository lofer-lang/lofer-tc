use std::fmt;

use substitution::substitute;

#[derive(Clone, PartialEq)]
pub enum Expression {
    Variable(usize), // variables should be indexed from the end of the list?

    IntroLambda {
        body: Box<Expression>,
    },
    ElimApplication {
        function: Box<Expression>,
        argument: Box<Expression>,
    },

    IntroPoint,

    IntroTT,
    IntroFF,
    ElimIf,

    IntroPair,
    ElimUncurry,

    IntroType(Box<Type>),
}

impl Expression {
    pub fn substitute(self: &Self, var: &Self) -> Self {
        substitute(self, 0, var)
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



impl fmt::Debug for Expression {
    fn fmt(self: &Self, fmt: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        let mut ctx = Vec::new();
        self.pretty(fmt, &mut ctx)?;
        Ok(())
    }
}

fn choose_var(len: usize) -> String {
    ["a", "b", "c", "d", "e", "f",
     "g", "h", "i", "j", "k", "l",
     "m", "n", "o", "p", "q", "r",
     "s", "t", "u", "v", "w", "x",
     "y", "z"][len % 26].into()
}

impl Expression {
    fn pretty(self: &Self, fmt: &mut fmt::Formatter, ctx: &mut Vec<String>)
        -> Result<(), fmt::Error>
    {
        use self::Expression::*;
        match *self {
            Variable(n) => {
                if n < ctx.len() {
                    write!(fmt, "{}", ctx[ctx.len() - n - 1])?;
                } else {
                    write!(fmt, "?")?;
                }
            },

            IntroLambda { ref body } => {
                let var = choose_var(ctx.len());
                write!(fmt, "\\{} -> ", var)?;
                ctx.push(var);
                body.pretty(fmt, ctx)?;
                ctx.pop();
            },
            ElimApplication { ref function, ref argument } => {
                let first_brackets = match **function {
                    IntroLambda { .. } => true,
                    _ => false,
                };

                let second_brackets = match **argument {
                    IntroLambda { .. } => true,
                    ElimApplication { .. } => true,
                    _ => false,
                };

                if first_brackets {
                    write!(fmt, "(")?;
                }
                function.pretty(fmt, ctx)?;
                if first_brackets {
                    write!(fmt, ")")?;
                }

                write!(fmt, " ")?;

                if second_brackets {
                    write!(fmt, "(")?;
                }
                argument.pretty(fmt, ctx)?;
                if second_brackets {
                    write!(fmt, ")")?;
                }
            },

            IntroPoint => {
                write!(fmt, "tt")?;
            },

            IntroTT => {
                write!(fmt, "true")?;
            },
            IntroFF => {
                write!(fmt, "false")?;
            },
            ElimIf => {
                write!(fmt, "bool_elim")?;
            },

            IntroPair => {
                // TODO print as tuples?
                // pair x (pair y z) => (x, y, z)?
                write!(fmt, "pair")?;
            },
            ElimUncurry => {
                write!(fmt, "sigma_elim")?;
            },

            IntroType(ref ty) => {
                ty.pretty(fmt, ctx)?;
            },
        }
        Ok(())
    }
}

impl Type {
    fn pretty(self: &Self, fmt: &mut fmt::Formatter, ctx: &mut Vec<String>)
        -> Result<(), fmt::Error> {
        use self::Type::*;
        match *self {
            Void => {
                write!(fmt, "Void")?;
            },
            Unit => {
                write!(fmt, "Unit")?;
            },
            Bool => {
                write!(fmt, "Bool")?;
            },

            Pi { ref domain, ref codomain } => {
                let var = choose_var(ctx.len());
                write!(fmt, "Pi {}: ", var)?;
                domain.pretty(fmt, ctx)?;
                write!(fmt, ", ")?;
                ctx.push(var);
                codomain.pretty(fmt, ctx)?;
                ctx.pop();
            },

            Sigma { ref fst_type, ref snd_type } => {
                let var = choose_var(ctx.len());
                write!(fmt, "Sigma {}: ", var)?;
                fst_type.pretty(fmt, ctx)?;
                write!(fmt, ", ")?;
                ctx.push(var);
                snd_type.pretty(fmt, ctx)?;
                ctx.pop();
            },

            Universe => {
                write!(fmt, "Type")?;
            },
        }
        Ok(())
    }
}

pub fn var(n: usize) -> Expression {
    Expression::Variable(n)
}

// could return point(),
// since this will never be applied to a value
pub fn absurd() -> Expression {
    lambda(var(0))
}

pub fn trivial() -> Expression {
    lambda(lambda(var(1)))
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
) -> Expression {
    let result = Expression::ElimIf;
    let result = apply(result, tt_branch);
    let result = apply(result, ff_branch);
    let result = apply(result, condition);
    result
}

pub fn lambda(body: Expression)
    -> Expression
{
    let body = Box::new(body);
    Expression::IntroLambda { body }
}

pub fn apply(function: Expression, argument: Expression) -> Expression {
    let function = Box::new(function);
    let argument = Box::new(argument);
    Expression::ElimApplication { function, argument }
}

// see if-then-else on the subject of type inference
pub fn pair(fst: Expression, snd: Expression) -> Expression {
    let result = Expression::IntroPair;
    let result = apply(result, fst);
    let result = apply(result, snd);
    result
}

pub fn uncurry(fun: Expression) -> Expression {
    let result = Expression::ElimUncurry;
    let result = apply(result, fun);
    result
}

pub fn fst(x: Expression) -> Expression {
    apply(uncurry(lambda(lambda(var(1)))), x)
}

pub fn snd(x: Expression) -> Expression {
    apply(uncurry(lambda(lambda(var(0)))), x)
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

pub fn fix(x: Expression) -> Expression {
    apply(
        lambda(apply(var(0), var(0))),
        lambda(apply(x, apply(var(0), var(0)))),
    )
}

#[cfg(test)]
mod tests {
    #[test]
    fn equality() {
        unimplemented!();
    }

    #[test]
    fn coinductive_equality() {
        unimplemented!();
    }

    #[test]
    fn pretty_printing() {
        unimplemented!();
    }
}

