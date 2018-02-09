use expressions::*;

pub fn substitute(expr: &Expression, i: usize, value: &Expression)
    -> Expression
{
    use expressions::Expression::*;
    match *expr {
        Variable(m) => {
            if m > i {
                Variable(m-1)
            } else if m == i {
                deepen(value, i, 0)
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
            use expressions::Type::*;
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

fn deepen(expr: &Expression, extra_depth: usize, current_offset: usize)
    -> Expression
{
    use expressions::Expression::*;
    match *expr {
        Variable(n) => {
            if n < current_offset {
                // variable is local to a lambda or something
                var(n)
            } else {
                var(n + extra_depth)
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
            let condition = deepen(condition, extra_depth, current_offset);
            let tt_branch = deepen(tt_branch, extra_depth, current_offset);
            let ff_branch = deepen(ff_branch, extra_depth, current_offset);
            let out_type = deepen(out_type, extra_depth, current_offset + 1);
            if_then_else(condition, tt_branch, ff_branch, out_type)
        },

        IntroLambda { ref in_type, ref body } => {
            let in_type = deepen(in_type, extra_depth, current_offset);
            let body = deepen(body, extra_depth, current_offset + 1);
            lambda(in_type, body)
        },
        ElimApplication { ref function, ref argument } => {
            let function = deepen(function, extra_depth, current_offset);
            let argument = deepen(argument, extra_depth, current_offset);
            apply(function, argument)
        },

        IntroPair { ref fst, ref snd, ref snd_type } => {
            let fst = deepen(fst, extra_depth, current_offset);
            let snd = deepen(snd, extra_depth, current_offset);
            let snd_type = deepen(snd_type, extra_depth, current_offset + 1);
            pair(fst, snd, snd_type)
        },
        ElimFst { ref pair } => {
            let pair = deepen(pair, extra_depth, current_offset);
            fst(pair)
        },
        ElimSnd { ref pair } => {
            let pair = deepen(pair, extra_depth, current_offset);
            snd(pair)
        },

        IntroType(ref typ) => {
            use expressions::Type::*;
            match **typ {
                Void | Unit | Bool | Universe => expr.clone(),
                Pi { ref domain, ref codomain } => {
                    let domain = deepen(domain, extra_depth, current_offset);
                    let codomain = deepen(codomain, extra_depth,
                                          current_offset + 1);
                    pi(domain, codomain)
                },
                Sigma { ref fst_type, ref snd_type } => {
                    let fst_type = deepen(fst_type, extra_depth,
                                          current_offset);
                    let snd_type = deepen(snd_type, extra_depth,
                                          current_offset + 1);
                    sigma(fst_type, snd_type)
                },
            }
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! substitutes {
        (($n: expr) <- ($A: expr) in $B: expr => $C: expr) => {{
            let n = $n;
            let var = $A;
            let before = $B;
            let after = substitute(&before, n, &var);
            assert_eq!($C, after);
        }}
    }

    #[test]
    fn basics() {
        // just write a test for each expression type to make sure it
        // substitutes correctly
        unimplemented!();
    }

    #[test]
    fn closed_substitution() {
        substitutes!((0) <- (tt()) in var(0) => tt());

        substitutes!(
            (0) <- (tt()) in lambda(bool(), var(0))
        =>
            lambda(bool(), var(0))
        );

        substitutes!(
            (0) <- (tt()) in lambda(bool(), var(1))
        =>
            lambda(bool(), tt())
        );

        substitutes!(
            (0) <- (tt()) in pair(var(0), var(1), bool())
        =>
            pair(tt(), var(0), bool())
        );
    }

    #[test]
    fn open_substitution() {
        substitutes!((0) <- (var(0)) in var(0) => var(0));

        substitutes!((1) <- (var(0)) in var(1) => var(1));

        substitutes!((1) <- (var(1)) in var(1) => var(2));

        substitutes!(
            (0) <- (lambda(bool(), var(0))) in var(0)
        =>
            lambda(bool(), var(0))
        );

        substitutes!(
            (0) <- (var(2)) in lambda(bool(), var(1))
        =>
            lambda(bool(), var(3))
        );
    }
}
