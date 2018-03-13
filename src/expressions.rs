#[derive(Clone, PartialEq)]
pub enum Expression {
    Variable {
        name: String,
    },

    IntroLambda {
        var_name: String,
        var_type: Box<Expression>,
        body: Box<Expression>,
    },
    ElimApplication {
        function: Box<Expression>,
        argument: Box<Expression>,
    },

    ElimAbsurd {
        output_type: Box<Expression>,
    },

    IntroPoint,
    ElimTrivial {
        predicate: Box<Expression>,
    },

    IntroTT,
    IntroFF,
    ElimIf {
        out_type: Box<Expression>,
    },

    IntroPair {
        fst_type: Box<Expression>,
        snd_type: Box<Expression>,
    },

    ElimUncurry {
        fst_type: Box<Expression>,
        snd_type: Box<Expression>,
    },

    IntroType(Box<Type>),

    // can be used to make `fix f = f (fix f)`, the fixpoint combinator
    // i.e. forall a: Type, (a -> a) -> a
    // which is useful for recursive types and functions
    // factorial = fix (\fact -> \x -> x * fact (x - 1))
    // compiles into (\f -> (\x -> x x) (\x -> f (x x)))
    SpecialFix {
        // is_co: bool, // is this necessary?
        output_type: Box<Expression>,
    }
}

#[derive(Clone, PartialEq)]
pub enum Type {
    Void,
    Unit,
    Bool,
    Pi {
        var_name: String,
        domain: Box<Expression>,
        codomain: Box<Expression>,
    },
    Sigma {
        var_name: String,
        fst_type: Box<Expression>,
        snd_type: Box<Expression>,
    },
    Universe/*(usize)*/,
}

/*
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
*/

fn find_var(ctx: &Vec<String>, var: &String) -> usize {
    for i in 0..ctx.len() {
        if ctx[ctx.len() - i - 1] == *var {
            return i;
        }
    }
    panic!("Variable not defined: `{}`", var);
}

/*
impl Expression {
    fn convert(self: &Self) -> programs::Expression {
        self.convert_with(&mut Vec::new())
    }

    fn convert_with(self: &Self, ctx: &mut Vec<String>)
        -> programs::Expression
    {
        use self::Expression::*;
        match *self {
            Var { ref name } => {
                let num = find_var(ctx, name);
                programs::var(num)
            },
            IntroLambda { ref var_name, ref body, .. } => {
                ctx.push(var_name);
                let body = body.convert(ctx);
                ctx.pop();
                programs::lambda(body)
            },
            ElimApplication { ref function, ref argument } => {
                let function = function.convert(ctx);
                let argument = argument.convert(ctx);
                programs::apply(function, argument)
            },

            ElimVoid => {
                // could return point(),
                // since this will never be applied to a value
                programs::lambda(programs::var(0))
            },

            IntroPoint => {
                programs::point()
            },
            ElimTrivial => {
                programs::lambda(programs::lambda(programs::var(1)))
            },

            IntroTT => {
                programs::tt()
            },
            IntroFF => {
                programs::ff()
            },
            ElimIf => {
                Elim
        }
    }
}
*/

/*
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

            IntroLambda { ref in_type, ref body } => {
                let var = choose_var(ctx.len());
                write!(fmt, "\\{}: ", var)?;
                in_type.pretty(fmt, ctx)?;
                write!(fmt, " -> ")?;
                ctx.push(var);
                body.pretty(fmt, ctx)?;
                ctx.pop();
            },
            ElimApplication { ref function, ref argument } => {
                write!(fmt, "(")?;
                function.pretty(fmt, ctx)?;
                write!(fmt, ") (")?;
                argument.pretty(fmt, ctx)?;
                write!(fmt, ")")?;
            },

            ElimAbsurd => {
                write!(fmt, "absurd")?;
            },

            IntroPoint => {
                write!(fmt, "<>")?;
            },
            ElimTrivial => {
                write!(fmt, "trivial")?;
            },

            IntroTT => {
                write!(fmt, "true")?;
            },
            IntroFF => {
                write!(fmt, "false")?;
            },
            ElimIf {
                ref condition,
                ref tt_branch,
                ref ff_branch,
                ..
            }=> {

                write!(fmt, "if ")?;
                condition.pretty(fmt, ctx)?;
                write!(fmt, " then ")?;
                tt_branch.pretty(fmt, ctx)?;
                write!(fmt, " else ")?;
                ff_branch.pretty(fmt, ctx)?;
            },

            IntroPair { ref fst, ref snd, .. } => {
                write!(fmt, "<<")?;
                fst.pretty(fmt, ctx)?;
                write!(fmt, ", ")?;
                snd.pretty(fmt, ctx)?;
                write!(fmt, ">>")?;
            },
            ElimFst { ref pair } => {
                write!(fmt, "p1 (")?;
                pair.pretty(fmt, ctx)?;
                write!(fmt, ")")?;
            },
            ElimSnd { ref pair } => {
                write!(fmt, "p2 (")?;
                pair.pretty(fmt, ctx)?;
                write!(fmt, ")")?;
            },

            IntroType(ref ty) => {
                ty.pretty(fmt, ctx)?;
            },

            SpecialFix { ref generator } => {
                write!(fmt, "fix (")?;
                generator.pretty(fmt, ctx)?;
                write!(fmt, ")")?;
            },
        }
        Ok(())
    }
}
*/

/*
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
*/

pub fn var<T: Into<String>>(name: T) -> Expression {
    let name = name.into();
    Expression::Variable { name }
}

pub fn lambda<T: Into<String>>(
    var_name: T,
    var_type: Expression,
    body: Expression,
) -> Expression {
    let var_name = var_name.into();
    let var_type = Box::new(var_type);
    let body = Box::new(body);
    Expression::IntroLambda { var_name, var_type, body }
}

pub fn apply(function: Expression, argument: Expression) -> Expression {
    let function = Box::new(function);
    let argument = Box::new(argument);
    Expression::ElimApplication { function, argument }
}

pub fn absurd(void: Expression, output_type: Expression) -> Expression {
    apply(absurd_fn(output_type), void)
}

pub fn absurd_fn(output_type: Expression) -> Expression {
    let output_type = Box::new(output_type);
    Expression::ElimAbsurd { output_type }
}

pub fn point() -> Expression {
    Expression::IntroPoint
}

pub fn trivial(predicate: Expression, case: Expression) -> Expression {
    apply(trivial_fn(predicate), case)
}

pub fn trivial_fn(predicate: Expression) -> Expression {
    let predicate = Box::new(predicate);
    Expression::ElimTrivial { predicate }
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
    let result = if_then_else_fn(out_type);
    let result = apply(result, tt_branch);
    let result = apply(result, ff_branch);
    let result = apply(result, condition);
    result
}

pub fn if_then_else_fn(out_type: Expression) -> Expression {
    let out_type = Box::new(out_type);
    Expression::ElimIf { out_type }
}

// see if-then-else on the subject of type inference
pub fn pair(
    fst: Expression,
    snd: Expression,
    fst_type: Expression,
    snd_type: Expression,
) -> Expression {
    let result = pair_fn(fst_type, snd_type);
    let result = apply(result, fst);
    let result = apply(result, snd);
    result
}

pub fn pair_fn(fst_type: Expression, snd_type: Expression) -> Expression {
    let fst_type = Box::new(fst_type);
    let snd_type = Box::new(snd_type);
    Expression::IntroPair { fst_type, snd_type }
}

pub fn uncurry(pair: Expression, fst_type: Expression, snd_type: Expression)
    -> Expression
{
    apply(uncurry_fn(fst_type, snd_type), pair)
}

pub fn uncurry_fn(fst_type: Expression, snd_type: Expression) -> Expression {
    let fst_type = Box::new(fst_type);
    let snd_type = Box::new(snd_type);
    Expression::ElimUncurry { fst_type, snd_type }
}

pub fn simple_type(typ: Type) -> Expression {
    let typ = Box::new(typ);
    Expression::IntroType(typ)
}

pub fn fix(output_type: Expression, generator: Expression) -> Expression {
    apply(fix_fn(output_type), generator)
}

pub fn fix_fn(output_type: Expression) -> Expression {
    let output_type = Box::new(output_type);
    Expression::SpecialFix { output_type }
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

pub fn pi<T: Into<String>>(
    var_name: T,
    domain: Expression,
    codomain: Expression,
) -> Expression {
    let var_name = var_name.into();
    let domain = Box::new(domain);
    let codomain = Box::new(codomain);
    let out = Type::Pi { var_name, domain, codomain };
    simple_type(out)
}

pub fn sigma<T: Into<String>>(
    var_name: T,
    fst_type: Expression,
    snd_type: Expression,
) -> Expression {
    let var_name = var_name.into();
    let fst_type = Box::new(fst_type);
    let snd_type = Box::new(snd_type);
    let out = Type::Sigma { var_name, fst_type, snd_type };
    simple_type(out)
}

pub fn universe() -> Expression {
    simple_type(Type::Universe)
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

