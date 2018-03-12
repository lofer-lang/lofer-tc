use programs::*;

pub fn reduce(expr: &Expression, is_strict: bool) -> Expression {
    use programs::Expression::*;
    match *expr {
        IntroLambda { ref body } => {
            let body = reduce(body, false);
            lambda(body)
        },
        ElimApplication { ref function, ref argument } => {
            let function = reduce(function, is_strict);
            if let IntroLambda { body, .. } = function {
                let result = body.substitute(argument);
                // ooo a tail call
                reduce(&result, is_strict)
            } else {
                unimplemented!();
                let argument = reduce(argument, is_strict);
                apply(function, argument)
            }
        },

        IntroType(ref typ) => {
            use programs::Type::*;
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

        _ => expr.clone(),
        /*
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
    */
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
    fn peano() {
        // these should be in a module somewhere since multiple tests could
        // use them
        let sum = || lambda(universe(), lambda(universe(),
            sigma(bool(), if_then_else(var(0), var(2), var(1), universe()))
        ));
        let apply_sum = |a, b| apply(apply(sum(), a), b);
        reduces!(
            apply_sum(bool(), unit())
        =>
            sigma(bool(), if_then_else(var(0), bool(), unit(), universe()))
        );

        let nat = || fix(lambda(universe(), apply_sum(var(0), unit())));

        let zero = || pair(ff(), point(), nat());
        let succ = || lambda(nat(), pair(tt(), var(0), nat()));
        let apply_succ = |x| apply(succ(), x);

        /* nope nope nope
        let nat_elim = ||
            lambda(pi(nat(), universe()),
            lambda(apply(var(0), zero()),
            lambda(
                pi(nat(),
                pi(apply(var(2), var(0)),
                    apply(var(3), apply(succ(), var(1)))
                )),
            fix(lambda(pi(nat(), apply(var(), var(0))),
                lambda(nat(), if_then_else(fst(var(0)), base, apply(ind, apply(self, snd(var(0)))), apply(prop, var(1)))))))))
                */

        // this probably won't type check as is
        let plus = ||
            lambda(nat(),
            fix(lambda(pi(nat(), nat()),
            lambda(nat(),
                if_then_else(
                    fst(var(0)),
                        apply(succ(),
                        apply(var(1),
                        snd(var(0)))),
                    var(2),
                    nat(),
                )
            ))));

        let two = || apply_succ(apply_succ(zero()));
        let four = || apply_succ(apply_succ(two())).reduce_lazy();

        reduces!(apply(apply(plus(), two()), two()) => four());
    }

    #[test]
    fn other_recursive_things() {
        unimplemented!();
    }
}

