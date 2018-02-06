use std::mem;

use type_system::{Type, Expression};

fn reduce(ctx: &mut Vec<Type>, expr: &mut Expression) {
    use type_system::Expression::*;
    while let Some(reduction) = match *expr {
        Variable(_) | IntroPoint | IntroTT | IntroFF => None,
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
        _ => unimplemented!(),
    } {
        *expr = reduction;
    }
}


#[cfg(test)]
mod tests {
    use type_system::Expression::*;

    use super::*;

    #[test]
    fn reduce_if() {
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
}

