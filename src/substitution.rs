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

#[cfg(test)]
mod tests {
    #[test]
    fn substitution() {
        // daunting
        unimplemented!();
    }
}
