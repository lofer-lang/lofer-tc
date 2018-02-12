use expressions::*;

pub fn reduce(expr: &Expression, is_strict: bool) -> Expression {
    use expressions::Expression::*;
    match *expr {
        Variable(_) | IntroPoint | IntroTT | IntroFF => expr.clone(),
        ElimIf {
            ref condition,
            ref tt_branch,
            ref ff_branch,
            ref out_type,
        } => {
            let condition = reduce(condition, is_strict);
            if let IntroTT = condition {
                reduce(tt_branch, is_strict)
            } else if let IntroFF = condition {
                reduce(ff_branch, is_strict)
            } else {
                let tt_branch = reduce(tt_branch, false);
                let ff_branch = reduce(ff_branch, false);
                let out_type = reduce(out_type, false);
                if_then_else(condition, tt_branch, ff_branch, out_type)
            }
        },

        IntroLambda { ref in_type, ref body } => {
            let in_type = reduce(in_type, false);
            let body = reduce(body, false);
            lambda(in_type, body)
        },
        ElimApplication { ref function, ref argument } => {
            let function = reduce(function, is_strict);
            if let IntroLambda { body, .. } = function {
                let result = body.substitute(argument);
                // ooo a tail call
                reduce(&result, is_strict)
            } else {
                let argument = reduce(argument, is_strict);
                apply(function, argument)
            }
        },

        IntroPair { ref fst, ref snd, ref snd_type } => {
            let fst = reduce(fst, is_strict);
            let snd = reduce(snd, is_strict);
            let snd_type = reduce(snd_type, false);
            pair(fst, snd, snd_type)
        },
        ElimFst { ref pair } => {
            let pair = reduce(pair, is_strict);
            if let IntroPair { fst, .. } = pair {
                *fst
            } else {
                fst(pair)
            }
        },
        ElimSnd { ref pair } => {
            let pair = reduce(pair, is_strict);
            if let IntroPair { snd, .. } = pair {
                reduce(&*snd, is_strict)
            } else {
                snd(pair)
            }
        },

        IntroType(ref typ) => {
            use expressions::Type::*;
            match **typ {
                Void | Unit | Bool | Universe => expr.clone(),
                Pi { ref domain, ref codomain } => {
                    let domain = reduce(domain, is_strict);
                    let codomain = reduce(codomain, is_strict);
                    pi(domain, codomain)
                },
                Sigma { ref fst_type, ref snd_type } => {
                    let fst_type = reduce(fst_type, is_strict);
                    let snd_type = reduce(snd_type, is_strict);
                    sigma(fst_type, snd_type)
                },
            }
        },

        SpecialFix { ref generator } => {
            let generator = reduce(generator, false);
            if is_strict {
                let fixed_point = fix(generator.clone());
                let expr = apply(generator, fixed_point);
                reduce(&expr, true)
            } else {
                fix(generator)
            }
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! irreducible {
        ($before: expr) => {{
            let before = $before;
            let after = reduce(&before, true);
            assert_eq!(before, after);
        }}
    }

    macro_rules! reduces {
        ($before: expr => $after: expr) => {{
            let before = $before;
            let after = reduce(&before, true);
            assert_eq!(after, $after);
        }}
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
        reduces!(apply(lambda(bool(), var(0)), tt()) => tt());

        reduces!(
            // (\x: Bool -> if x then ff else tt) tt
            apply(
                lambda(
                    bool(),
                    if_then_else(var(0), ff(), tt(), bool()),
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

    #[test]
    fn branches_block_recursion() {
        // not allowed in Agda or Coq
        // freeze = fix (\freeze: Void -> freeze)
        let freeze = || fix(lambda(void(), var(0)));

        // recursive things don't reduce until a branch is chosen
        irreducible!(if_then_else(var(0), freeze(), freeze(), void()));

        let term = ||
            fix(lambda(bool(), if_then_else(var(1), var(0), tt(), bool())));

        reduces!(
            term()
        =>
            if_then_else(var(0), term(), tt(), bool())
        );

        // not sure if this is necessary but recursive things don't
        // reduce until functions have been applied
        irreducible!(lambda(bool(), freeze()));

        let term = ||
            fix(
                lambda(
                    pi(bool(), bool()),
                    lambda(bool(), apply(var(1), var(0)))
                )
            );
        reduces!(
            term()
        =>
            lambda(bool(), apply(term(), var(0)))
        );
    }

    #[test]
    fn more_recursion_tests() {
        unimplemented!();
    }
}

