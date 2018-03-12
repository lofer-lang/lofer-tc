use programs::*;

pub fn substitute(expr: &Expression, i: usize, value: &Expression)
    -> Expression
{
    use programs::Expression::*;
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

        IntroLambda { ref body } => {
            let body = substitute(body, i+1, value);
            lambda(body)
        },
        ElimApplication { ref function, ref argument } => {
            let function = substitute(function, i, value);
            let argument = substitute(argument, i, value);
            apply(function, argument)
        },

        IntroType(ref typ) => {
            use programs::Type::*;
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

        _ => expr.clone(),
    }
}

pub fn deepen(expr: &Expression, extra_depth: usize, current_offset: usize)
    -> Expression
{
    use programs::Expression::*;
    match *expr {
        Variable(n) => {
            if n < current_offset {
                // variable is local to a lambda or something
                var(n)
            } else {
                var(n + extra_depth)
            }
        },

        IntroLambda { ref body } => {
            let body = deepen(body, extra_depth, current_offset + 1);
            lambda(body)
        },
        ElimApplication { ref function, ref argument } => {
            let function = deepen(function, extra_depth, current_offset);
            let argument = deepen(argument, extra_depth, current_offset);
            apply(function, argument)
        },

        IntroType(ref typ) => {
            use programs::Type::*;
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

        _ => expr.clone(),
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

        substitutes!((0) <- (var(1)) in var(0) => var(1));

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
