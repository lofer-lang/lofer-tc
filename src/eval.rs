use type_system::{Expression};

fn reduce(expr: &Expression) -> Expression {
    use type_system::Expression::*;
    match *expr {
        Variable(_) | IntroPoint | IntroTT | IntroFF => expr.clone(),
        ElimIf { ref condition, ref tt_branch, ref ff_branch } => {
            let condition = box_reduce(condition);
            if let IntroTT = *condition {
                reduce(tt_branch)
            } else if let IntroFF = *condition {
                reduce(ff_branch)
            } else {
                let tt_branch = box_reduce(tt_branch);
                let ff_branch = box_reduce(ff_branch);
                ElimIf { condition, tt_branch, ff_branch }
            }
        },

        IntroPair { ref fst, ref snd } => {
            let fst = box_reduce(fst);
            // is there some way of removing this line?
            // since we substitute during the p2/snd eliminator anyway
            // in fact sigma variables only matter for type checking
            let snd = substitute(snd, 1, &fst, false);
            let snd = box_reduce(&snd);
            IntroPair { fst, snd }
        },
        ElimFst { ref pair } => {
            let pair = reduce(pair);
            if let IntroPair { fst, .. } = pair {
                *fst
            } else {
                pair
            }
        },
        ElimSnd { ref pair } => {
            let pair = reduce(pair);
            if let IntroPair { fst, snd } = pair {
                // mainly to eliminate the variable
                let snd = substitute(&snd, 1, &fst, true);
                reduce(&snd)
            } else {
                pair
            }
        },
        _ => unimplemented!(),
    }
}

fn box_reduce(expr: &Expression)
    -> Box<Expression>
{
    Box::new(reduce(expr))
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

fn box_substitute(expr: &Expression, i: usize, value: &Expression, elim: bool)
    -> Box<Expression>
{
    Box::new(substitute(expr, i, value, elim))
}

#[cfg(test)]
mod tests {
    use type_system::Expression::*;

    use super::*;

    macro_rules! irreducible {
        ($before: expr) => {
            let before = $before;
            let after = reduce(&before);
            assert_eq!(before, after);
        }
    }

    macro_rules! reduces {
        ($before: expr => $after: expr) => {
            let before = $before;
            let after = reduce(&before);
            assert_eq!(after, $after);
        }
    }

    #[test]
    fn substitution() {
        // daunting
        unimplemented!();
    }

    #[test]
    fn irreducible_intros() {
        unimplemented!();
    }

    #[test]
    fn reduce_bool() {
        reduces!(
            // if tt then tt else ff
            ElimIf {
                condition: Box::new(IntroTT),
                tt_branch: Box::new(IntroTT),
                ff_branch: Box::new(IntroFF),
            }
        =>
            // tt
            IntroTT
        );

        reduces!(
            // if ff then tt else ff
            ElimIf {
                condition: Box::new(IntroFF),
                tt_branch: Box::new(IntroTT),
                ff_branch: Box::new(IntroFF),
            }
        =>
            // ff
            IntroFF
        );

        irreducible!(
            // if x then tt else ff
            ElimIf {
                condition: Box::new(Variable(1)),
                tt_branch: Box::new(IntroTT),
                ff_branch: Box::new(IntroFF),
            }
        );
    }

    #[test]
    fn reduce_pair() {
        reduces!(
            // p1 <tt, ff>
            ElimFst {
                pair: Box::new(IntroPair {
                    fst: Box::new(IntroTT),
                    snd: Box::new(IntroFF),
                }),
            }
        =>
            // tt
            IntroTT
        );

        reduces!(
            // p2 <tt, ff>
            ElimSnd {
                pair: Box::new(IntroPair {
                    fst: Box::new(IntroTT),
                    snd: Box::new(IntroFF),
                }),
            }
        =>
            //ff
            IntroFF
        );

        irreducible!(
            // p1 x
            ElimFst {
                pair: Box::new(Variable(1)),
            }
        );

        irreducible!(
            // p2 x
            ElimSnd {
                pair: Box::new(Variable(1)),
            }
        );
    }
}

