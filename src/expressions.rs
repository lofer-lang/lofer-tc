use std::fmt;

use eval::reduce;
use substitution::substitute;

#[derive(Clone)]
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

    // can be used to make `fix f = f (fix f)`, the fixpoint combinator
    // i.e. forall a: Type, (a -> a) -> a
    // which is useful for recursive types and functions
    // factorial = fix (\fact -> \x -> x * fact (x - 1))
    SpecialFix {
        // is_co: bool,  // is this necessary?
        generator: Box<Expression>,
    },
}

impl Expression {
    pub fn substitute(self: &Self, var: &Self) -> Self {
        substitute(self, 0, var)
    }

    pub fn reduce_lazy(self: &Self) -> Self {
        reduce(self, false)
    }
    pub fn reduce_strict(self: &Self) -> Self {
        reduce(self, true)
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

// compares `fix(gen_l)` with `other`, by expanding the fix once and reducing
fn compare_fix(generator: &Expression, right: &Expression) -> bool {
    let left = apply(generator.clone(), fix(generator.clone()));
    let left = left.reduce_lazy();
    left == *right
}


impl PartialEq for Expression {
    fn eq(self: &Self, other: &Self) -> bool {
        use self::Expression::*;
        match (self, other) {
            (&SpecialFix { generator: ref gen_l },
             &SpecialFix { generator: ref gen_r }) => {
                gen_l == gen_r
            },
            (&SpecialFix { ref generator }, _) => {
                compare_fix(generator, other)
            },
            (_, &SpecialFix { ref generator }) => {
                compare_fix(generator, self)
            },

            // the rest are all really boring... exactly like #[derive()]
            (&Variable(n), &Variable(m)) => n == m,

            (&IntroPoint, &IntroPoint) => true,

            (&IntroTT, &IntroTT) => true,
            (&IntroFF, &IntroFF) => true,
            (
                &ElimIf {
                    condition: ref l_con,
                    tt_branch: ref l_tt,
                    ff_branch: ref l_ff,
                    out_type: ref l_out,
                },
                &ElimIf {
                    condition: ref r_con,
                    tt_branch: ref r_tt,
                    ff_branch: ref r_ff,
                    out_type: ref r_out,
                },
            ) => {
                let con_eq = l_con == r_con;
                let tt_eq = l_tt == r_tt;
                let ff_eq = l_ff == r_ff;
                let out_eq = l_out == r_out;
                con_eq && tt_eq && ff_eq && out_eq
            },

            (
                &IntroLambda {
                    in_type: ref l_in,
                    body: ref l_body,
                },
                &IntroLambda {
                    in_type: ref r_in,
                    body: ref r_body,
                },
            ) => {
                let in_eq = l_in == r_in;
                let body_eq = l_body == r_body;
                in_eq && body_eq
            },
            (
                &ElimApplication {
                    function: ref l_fun,
                    argument: ref l_arg,
                },
                &ElimApplication {
                    function: ref r_fun,
                    argument: ref r_arg,
                },
            ) => {
                let fun_eq = l_fun == r_fun;
                let arg_eq = l_arg == r_arg;
                fun_eq && arg_eq
            },

            (
                &IntroPair {
                    fst: ref l_fst,
                    snd: ref l_snd,
                    snd_type: ref l_st,
                },
                &IntroPair {
                    fst: ref r_fst,
                    snd: ref r_snd,
                    snd_type: ref r_st,
                },
            ) => {
                let fst_eq = l_fst == r_fst;
                let snd_eq = l_snd == r_snd;
                let st_eq = l_st == r_st;
                fst_eq && snd_eq && st_eq
            },
            (
                &ElimFst {
                    pair: ref l_pair,
                },
                &ElimFst {
                    pair: ref r_pair,
                },
            ) => {
                l_pair == r_pair
            },
            (
                &ElimSnd {
                    pair: ref l_pair,
                },
                &ElimSnd {
                    pair: ref r_pair,
                },
            ) => {
                l_pair == r_pair
            },

            (&IntroType(ref l_ty), &IntroType(ref r_ty)) => {
                l_ty == r_ty
            },

            (_, _) => false,
        }
    }
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

            IntroPoint => {
                write!(fmt, "<>")?;
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

pub fn fix(generator: Expression) -> Expression {
    let generator = Box::new(generator);
    Expression::SpecialFix { generator }
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

