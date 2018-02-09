use type_system::{Expression};

pub fn reduce(expr: &Expression) -> Expression {
    use type_system::Expression::*;
    use type_system::expressions::*;
    match *expr {
        Variable(_) | IntroPoint | IntroTT | IntroFF => expr.clone(),
        ElimIf {
            ref condition,
            ref tt_branch,
            ref ff_branch,
            ref out_type,
        } => {
            let condition = reduce(condition);
            if let IntroTT = condition {
                reduce(tt_branch)
            } else if let IntroFF = condition {
                reduce(ff_branch)
            } else {
                let tt_branch = reduce(tt_branch);
                let ff_branch = reduce(ff_branch);
                let out_type = reduce(out_type);
                if_then_else(condition, tt_branch, ff_branch, out_type)
            }
        },

        IntroLambda { ref in_type, ref body } => {
            let in_type = reduce(in_type);
            let body = reduce(body);
            lambda(in_type, body)
        },
        ElimApplication { ref function, ref argument } => {
            let function = reduce(function);
            if let IntroLambda { body, .. } = function {
                let result = substitute(&body, 1, argument);
                // ooo a tail call
                reduce(&result)
            } else {
                let argument = reduce(argument);
                apply(function, argument)
            }
        },

        IntroPair { ref fst, ref snd, ref snd_type } => {
            let fst = reduce(fst);
            let snd = reduce(snd);
            let snd_type = reduce(snd_type);
            pair(fst, snd, snd_type)
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
            if let IntroPair { snd, .. } = pair {
                reduce(&*snd)
            } else {
                snd(pair)
            }
        },

        IntroType(ref typ) => {
            use type_system::Type::*;
            match **typ {
                Void | Unit | Bool | Universe => expr.clone(),
                Pi { ref domain, ref codomain } => {
                    let domain = reduce(domain);
                    let codomain = reduce(codomain);
                    pi(domain, codomain)
                },
                Sigma { ref fst_type, ref snd_type } => {
                    let fst_type = reduce(fst_type);
                    let snd_type = reduce(snd_type);
                    sigma(fst_type, snd_type)
                },
            }
        },
    }
}

pub fn substitute(expr: &Expression, i: usize, value: &Expression)
    -> Expression
{
    use type_system::Expression::*;
    use type_system::expressions::*;
    match *expr {
        Variable(m) => {
            if m > i {
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
        ElimIf {
            ref condition,
            ref tt_branch,
            ref ff_branch,
            ref out_type,
        } => {
            let condition = substitute(condition, i, value);
            let tt_branch = substitute(tt_branch, i, value);
            let ff_branch = substitute(ff_branch, i, value);
            let out_type = substitute(out_type, i+1, value);
            if_then_else(condition, tt_branch, ff_branch, out_type)
        },

        IntroLambda { ref in_type, ref body } => {
            let in_type = substitute(in_type, i, value);
            let body = substitute(body, i+1, value);
            lambda(in_type, body)
        },
        ElimApplication { ref function, ref argument } => {
            let function = substitute(function, i, value);
            let argument = substitute(argument, i, value);
            apply(function, argument)
        },

        IntroPair { ref fst, ref snd, ref snd_type } => {
            let fst = substitute(fst, i, value);
            let snd = substitute(snd, i, value);
            let snd_type = substitute(snd_type, i+1, value);
            pair(fst, snd, snd_type)
        },
        ElimFst { ref pair } => {
            let pair = substitute(pair, i, value);
            fst(pair)
        },
        ElimSnd { ref pair } => {
            let pair = substitute(pair, i, value);
            snd(pair)
        },

        IntroType(ref typ) => {
            use type_system::Type::*;
            match **typ {
                Void | Unit | Bool | Universe => expr.clone(),
                Pi { ref domain, ref codomain } => {
                    let domain = substitute(domain, i, value);
                    let codomain = substitute(codomain, i+1, value);
                    pi(domain, codomain)
                },
                Sigma { ref fst_type, ref snd_type } => {
                    let fst_type = substitute(fst_type, i, value);
                    let snd_type = substitute(snd_type, i+1, value);
                    sigma(fst_type, snd_type)
                },
            }
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
        irreducible!(pair(tt(), ff(), bool()));
    }

    #[test]
    fn reduce_bool() {
        reduces!(if_then_else(tt(), tt(), ff(), bool()) => tt());

        reduces!(if_then_else(ff(), tt(), ff(), bool()) => ff());

        irreducible!(if_then_else(var(1), tt(), ff(), bool()));
    }

    #[test]
    fn reduce_lambda() {
        reduces!(apply(lambda(bool(), var(1)), tt()) => tt());

        reduces!(
            // (\x: Bool -> if x then ff else tt) tt
            apply(
                lambda(
                    bool(),
                    if_then_else(var(1), ff(), tt(), bool()),
                ),
                tt(),
            )
        =>
            ff()
        );

        irreducible!(apply(var(1), point()));
    }

    #[test]
    fn reduce_pair() {
        reduces!(fst(pair(tt(), ff(), bool())) => tt());
        reduces!(snd(pair(tt(), ff(), bool())) => ff());

        irreducible!(fst(var(1)));
        irreducible!(snd(var(1)));
    }
}

