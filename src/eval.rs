use std::mem;

use type_system;
use type_system::{Type, Expression};

// TODO is ctx needed?
fn reduce(ctx: &mut Vec<Type>, expr: &mut Expression) {
    use type_system::Expression::*;
    while let Some(reduction) = match *expr {
        Variable(_) | IntroPoint | IntroTT | IntroFF => None,
        IntroPair { ref mut fst, ref mut snd } => {
            reduce(ctx, fst);
            let maybe_fst_type = type_system::type_check(ctx, fst);
            let fst_type = maybe_fst_type
                .expect("Type error when substituting");
            ctx.push(fst_type);
            // is there some way of removing this line?
            **snd = substitute(snd, 1, fst, false);
            reduce(ctx, snd);
            ctx.pop();

            None
        },

        ElimIf { ref mut condition, ref mut tt_branch, ref mut ff_branch } => {
            reduce(ctx, condition);
            if let IntroTT = **condition {
                Some(mem::replace(&mut **tt_branch, IntroPoint))
            } else if let IntroFF = **condition {
                Some(mem::replace(&mut **ff_branch, IntroPoint))
            } else {
                reduce(ctx, tt_branch);
                reduce(ctx, ff_branch);
                None
            }
        },
        ElimFst { ref mut pair } => {
            reduce(ctx, pair);
            if let IntroPair { ref mut fst, .. } = **pair {
                Some(mem::replace(&mut **fst, IntroPoint))
            } else {
                None
            }
        },
        ElimSnd { ref mut pair } => {
            reduce(ctx, pair);
            // rust doesn't yet like disjoint mutable reborrows on boxes
            let pair = &mut **pair;
            if let IntroPair { ref mut fst, ref mut snd } = *pair {
                Some(substitute(snd, 1, fst, true))
            } else {
                None
            }
        },
        _ => unimplemented!(),
    } {
        *expr = reduction;
    }
}

fn box_substitute(expr: &Expression, i: usize, value: &Expression, elim: bool)
    -> Box<Expression>
{
    Box::new(substitute(expr, i, value, elim))
}

fn substitute(expr: &Expression, i: usize, value: &Expression, elim: bool)
    -> Expression
{
    use type_system::Expression::*;
    match *expr {
        Variable(m) => {
            if m > i && elim {
                Variable(m-1)
            } else if m == i {
                value.clone()
            } else {
                Variable(m)
            }
        },

        IntroPoint | IntroTT | IntroFF => {
            expr.clone()
        },
        ElimIf { ref condition, ref tt_branch, ref ff_branch } => {
            ElimIf {
                condition: box_substitute(condition, i, value, elim),
                tt_branch: box_substitute(tt_branch, i, value, elim),
                ff_branch: box_substitute(ff_branch, i, value, elim),
            }
        },

        IntroLambda { ref variable, ref body } => {
            IntroLambda {
                variable: variable.clone(),
                body: box_substitute(body, i+1, value, elim),
            }
        },
        ElimApplication { ref function, ref argument } => {
            ElimApplication {
                function: box_substitute(function, i, value, elim),
                argument: box_substitute(argument, i, value, elim),
            }
        },

        IntroPair { ref fst, ref snd } => {
            IntroPair {
                fst: box_substitute(fst, i, value, elim),
                snd: box_substitute(snd, i+1, value, elim),
            }
        },
        ElimFst { ref pair } => {
            ElimFst {
                pair: box_substitute(pair, i, value, elim),
            }
        },
        ElimSnd { ref pair } => {
            ElimSnd {
                pair: box_substitute(pair, i, value, elim),
            }
        },
    }
}

#[cfg(test)]
mod tests {
    use type_system::Expression::*;

    use super::*;

    #[test]
    fn substitution() {
        unimplemented!();
    }

    #[test]
    fn reduce_bool() {
        let mut ctx = Vec::new();

        // if tt then tt else ff
        let mut expr = ElimIf {
            condition: Box::new(IntroTT),
            tt_branch: Box::new(IntroTT),
            ff_branch: Box::new(IntroFF),
        };
        reduce(&mut ctx, &mut expr);
        // tt
        assert_eq!(expr, IntroTT);

        // if ff then tt else ff
        let mut expr = ElimIf {
            condition: Box::new(IntroFF),
            tt_branch: Box::new(IntroTT),
            ff_branch: Box::new(IntroFF),
        };
        reduce(&mut ctx, &mut expr);
        // ff
        assert_eq!(expr, IntroFF);

        // if x then tt else ff
        let before = ElimIf {
            condition: Box::new(Variable(1)),
            tt_branch: Box::new(IntroTT),
            ff_branch: Box::new(IntroFF),
        };
        let mut after = before.clone();
        reduce(&mut ctx, &mut after);
        // irreducible
        assert_eq!(before, after);
    }

    #[test]
    fn reduce_pair() {
        let mut ctx = Vec::new();

        // p1 <tt, ff>
        let mut expr = ElimFst {
            pair: Box::new(IntroPair {
                fst: Box::new(IntroTT),
                snd: Box::new(IntroFF),
            }),
        };
        reduce(&mut ctx, &mut expr);
        // tt
        assert_eq!(expr, IntroTT);

        // p2 <tt, ff>
        let mut expr = ElimSnd {
            pair: Box::new(IntroPair {
                fst: Box::new(IntroTT),
                snd: Box::new(IntroFF),
            }),
        };
        reduce(&mut ctx, &mut expr);
        // ff
        assert_eq!(expr, IntroFF);

        // p1 x
        let before = ElimFst {
            pair: Box::new(Variable(1)),
        };
        let mut after = before.clone();
        reduce(&mut ctx, &mut after);
        // irreducible
        assert_eq!(before, after);

        // p2 x
        let before = ElimSnd {
            pair: Box::new(Variable(1)),
        };
        let mut after = before.clone();
        reduce(&mut ctx, &mut after);
        // irreducible
        assert_eq!(before, after);
    }
}

