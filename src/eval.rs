use type_system::{Expression};

fn reduce(expr: &Expression) -> Expression {
    use type_system::Expression::*;
    use type_system::expressions::*;
    match *expr {
        Variable(_) | IntroPoint | IntroTT | IntroFF => expr.clone(),
        ElimIf { ref condition, ref tt_branch, ref ff_branch } => {
            let condition = reduce(condition);
            if let IntroTT = condition {
                reduce(tt_branch)
            } else if let IntroFF = condition {
                reduce(ff_branch)
            } else {
                let tt_branch = reduce(tt_branch);
                let ff_branch = reduce(ff_branch);
                if_then_else(condition, tt_branch, ff_branch)
            }
        },

        IntroLambda { ref in_type, ref body } => {
            let in_type = (**in_type).clone();  // TODO reduce() this
            let body = reduce(body);
            lambda(in_type, body)
        },
        ElimApplication { ref function, ref argument } => {
            let function = reduce(function);
            if let IntroLambda { body, .. } = function {
                let result = substitute(&body, 1, argument, true);
                // ooo a tail call
                reduce(&result)
            } else {
                let argument = reduce(argument);
                apply(function, argument)
            }
        },

        IntroPair { ref fst, ref snd } => {
            let fst = reduce(fst);
            // is there some way of removing this line?
            // since we substitute during the p2/snd eliminator anyway
            // in fact sigma variables only matter for type checking
            let snd = substitute(snd, 1, &fst, false);
            let snd = reduce(&snd);
            pair(fst, snd)
        },
        ElimFst { ref pair } => {
            let pair = reduce(pair);
            if let IntroPair { fst, .. } = pair {
                *fst
            } else {
                fst(pair)
            }
        },
        ElimSnd { ref pair } => {
            let pair = reduce(pair);
            if let IntroPair { fst, snd } = pair {
                // mainly to eliminate the variable
                let snd = substitute(&snd, 1, &fst, true);
                reduce(&snd)
            } else {
                snd(pair)
            }
        },
    }
}

fn substitute(expr: &Expression, i: usize, value: &Expression, elim: bool)
    -> Expression
{
    use type_system::Expression::*;
    use type_system::expressions::*;
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
            let condition = substitute(condition, i, value, elim);
            let tt_branch = substitute(tt_branch, i, value, elim);
            let ff_branch = substitute(ff_branch, i, value, elim);
            if_then_else(condition, tt_branch, ff_branch)
        },

        IntroLambda { ref in_type, ref body } => {
            let in_type = (**in_type).clone();
            let body = substitute(body, i+1, value, elim);
            lambda(in_type, body)
        },
        ElimApplication { ref function, ref argument } => {
            let function = substitute(function, i, value, elim);
            let argument = substitute(argument, i, value, elim);
            apply(function, argument)
        },

        IntroPair { ref fst, ref snd } => {
            let fst = substitute(fst, i, value, elim);
            let snd = substitute(snd, i+1, value, elim);
            pair(fst, snd)
        },
        ElimFst { ref pair } => {
            let pair = substitute(pair, i, value, elim);
            fst(pair)
        },
        ElimSnd { ref pair } => {
            let pair = substitute(pair, i, value, elim);
            snd(pair)
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use type_system::expressions::*;

    macro_rules! irreducible {
        ($before: expr) => {{
            let before = $before;
            let after = reduce(&before);
            assert_eq!(before, after);
        }}
    }

    macro_rules! reduces {
        ($before: expr => $after: expr) => {{
            let before = $before;
            let after = reduce(&before);
            assert_eq!(after, $after);
        }}
    }

    #[test]
    fn substitution() {
        // daunting
        unimplemented!();
    }

    #[test]
    fn irreducible_intros() {
        irreducible!(point());
        irreducible!(tt());
        irreducible!(ff());
        irreducible!(lambda(unit(), point()));
        irreducible!(pair(tt(), ff()));
    }

    #[test]
    fn reduce_bool() {
        reduces!(if_then_else(tt(), tt(), ff()) => tt());

        reduces!(if_then_else(ff(), tt(), ff()) => ff());

        irreducible!(if_then_else(var(1), tt(), ff()));
    }

    #[test]
    fn reduce_lambda() {
        reduces!(apply(lambda(bool(), var(1)), tt()) => tt());

        reduces!(
            // (\x: Bool -> if x then ff else tt) tt
            apply(lambda(bool(), if_then_else(var(1), ff(), tt())), tt())
        =>
            ff()
        );

        irreducible!(apply(var(1), point()));
    }

    #[test]
    fn reduce_pair() {
        reduces!(fst(pait(tt(), ff())) => tt());
        reduces!(snd(pait(tt(), ff())) => ff());

        irreducible!(fst(var(1)));
        irreducible!(snd(var(1)));
    }
}

