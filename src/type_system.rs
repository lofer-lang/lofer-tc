#[derive(Clone, PartialEq, Debug)]
pub enum Expression {
    Variable(usize), // variables should be indexed from the end of the list?

    IntroPoint,

    IntroTT,
    IntroFF,
    ElimIf {
        condition: Box<Expression>,
        tt_branch: Box<Expression>,
        ff_branch: Box<Expression>,
    },

    IntroLambda {
        in_type: Box<Type>,
        body: Box<Expression>,
    },
    ElimApplication {
        function: Box<Expression>,
        argument: Box<Expression>,
    },

    IntroPair {
        fst: Box<Expression>,
        snd: Box<Expression>,
    },
    ElimFst {
        pair: Box<Expression>,
    },
    ElimSnd {
        pair: Box<Expression>,
    },
}

pub mod expressions {
    use super::Expression;
    use super::Type;

    pub fn var(n: usize) -> Expression {
        Expression::Variable(n)
    }

    pub fn point() -> Expression {
        Expression::IntroPoint
    }

    pub fn tt() -> Expression {
        Expression::IntroTT
    }

    pub fn ff() -> Expression {
        Expression::IntroFF
    }

    pub fn if_then_else(
        condition: Expression,
        tt_branch: Expression,
        ff_branch: Expression,
    ) -> Expression {
        let condition = Box::new(condition);
        let tt_branch = Box::new(tt_branch);
        let ff_branch = Box::new(ff_branch);
        Expression::ElimIf { condition, tt_branch, ff_branch }
    }

    pub fn lambda(in_type: Type, body: Expression)
        -> Expression
    {
        let in_type = Box::new(in_type);
        let body = Box::new(body);
        Expression::IntroLambda { in_type, body }
    }

    pub fn apply(function: Expression, argument: Expression) -> Expression {
        let function = Box::new(function);
        let argument = Box::new(argument);
        Expression::ElimApplication { function, argument }
    }

    pub fn pair(fst: Expression, snd: Expression) -> Expression {
        let fst = Box::new(fst);
        let snd = Box::new(snd);
        Expression::IntroPair { fst, snd }
    }

    pub fn fst(pair: Expression) -> Expression {
        let pair = Box::new(pair);
        Expression::ElimFst { pair }
    }

    pub fn snd(pair: Expression) -> Expression {
        let pair = Box::new(pair);
        Expression::ElimSnd { pair }
    }

    // the following return Type not Expression
    // but that will change next commit
    pub fn void() -> Type {
        Type::Void
    }

    pub fn unit() -> Type {
        Type::Unit
    }

    pub fn bool() -> Type {
        Type::Bool
    }

    pub fn pi(domain: Type, codomain: Type) -> Type {
        let domain = Box::new(domain);
        let codomain = Box::new(codomain);
        Type::Pi { domain, codomain }
    }

    pub fn sigma(fst_type: Type, snd_type: Type) -> Type {
        let fst_type = Box::new(fst_type);
        let snd_type = Box::new(snd_type);
        Type::Sigma { fst_type, snd_type }
    }
}

#[derive(Clone, PartialEq, Debug)]
pub enum Type {
    Void,
    Unit,
    Bool,
    Pi {
        domain: Box<Type>,
        codomain: Box<Type>,
    },
    Sigma {
        fst_type: Box<Type>,
        snd_type: Box<Type>,
    },
}

pub fn type_check(ctx: &mut Vec<Type>, expr: &Expression) -> Result<Type, ()> {
    use self::Expression::*;
    use self::expressions::*;
    match *expr {
        Variable(i) => {
            Ok(ctx[ctx.len() - i].clone())
        },

        IntroPoint => {
            Ok(unit())
        },

        IntroTT | IntroFF => {
            Ok(bool())
        },
        ElimIf { ref condition, ref tt_branch, ref ff_branch } => {
            let condition_type = type_check(ctx, condition)?;
            if let Type::Bool = condition_type {
                let tt_check = type_check(ctx, tt_branch)?;
                let ff_check = type_check(ctx, ff_branch)?;
                if tt_check == ff_check {
                    Ok(tt_check)
                } else {
                    Err(())
                }
            } else {
                Err(())
            }
        },

        IntroLambda { ref in_type, ref body } => {
            let in_type_clone = (**in_type).clone();
            ctx.push(in_type_clone);
            let maybe_codomain = type_check(ctx, body);
            let domain = ctx.pop().unwrap();
            let codomain = maybe_codomain?;
            Ok(pi(domain, codomain))
        },
        ElimApplication { ref function, ref argument } => {
            let fun_type = type_check(ctx, function)?;
            let arg_type = type_check(ctx, argument)?;
            if let Type::Pi { domain, codomain } = fun_type {
                if arg_type == *domain {
                    Ok(*codomain)
                } else {
                    Err(())
                }
            } else {
                Err(())
            }
        },

        IntroPair { ref fst, ref snd } => {
            let fst_type = type_check(ctx, fst)?;
            ctx.push(fst_type);
            let maybe_snd_type = type_check(ctx, snd);
            let fst_type = ctx.pop().unwrap();
            let snd_type = maybe_snd_type?;
            Ok(sigma(fst_type, snd_type))
        },
        ElimFst { ref pair } => {
            let pair_type = type_check(ctx, pair)?;
            if let Type::Sigma { fst_type, .. } = pair_type {
                Ok(*fst_type)
            } else {
                Err(())
            }
        },
        ElimSnd { ref pair } => {
            let pair_type = type_check(ctx, pair)?;
            if let Type::Sigma { snd_type, .. } = pair_type {
                Ok(*snd_type)
            } else {
                Err(())
            }
        },
    }
}



#[cfg(test)]
mod tests {
    use super::*;
    use super::expressions::*;

    macro_rules! type_checks {
        ($before: expr => $after: expr) => {{
            let mut ctx = Vec::new();
            let before = $before;
            let after = type_check(&mut ctx, &before);
            assert_eq!(Ok($after), after);
            // mainly for `variable_management` but should always pass
            assert_eq!(*ctx, []);
        }}
    }

    macro_rules! type_error {
        ($expr: expr) => {{
            let mut ctx = Vec::new();
            let expr = $expr;
            let after = type_check(&mut ctx, &before);
            assert_eq!(Err(()), after);
            assert_eq!(*ctx, []);
        }}
    }

    #[test]
    fn discrete_type_checking() {
        type_checks!(point() => unit());

        type_checks!(tt() => bool());

        type_checks!(ff() => bool());

        type_checks!(if_then_else(tt(), point(), point()) => unit());

        type_error!(if_then_else(point(), tt(), tt()));

        type_error!(if_then_else(tt(), tt(), point()));
    }

    #[test]
    fn function_type_checking() {
        type_checks!(lambda(unit(), var(1)) => pi(unit(), unit()));

        type_checks!(apply(lambda(bool(), point()), tt()) => unit());

        type_error!(apply(lambda(bool(), point()), point()));

        type_error!(apply(point(), tt()));
    }

    #[test]
    fn pair_type_checking() {
        type_checks!(pair(point(), tt()) => sigma(unit(), bool()));

        type_checks!(fst(pair(point(), tt())) => unit());

        type_checks!(snd(pair(point(), tt())) => bool());

        type_error!(fst(point()));

        type_error!(snd(point()));
    }

    // passes since sigma will be dependent in the future
    #[test]
    fn strange_diagonal() {
        // unusual to represent this way, but equivalent to <tt, tt>
        type_checks!(pair(tt(), var(1)) => sigma(bool(), bool()));
    }

    #[test]
    fn variable_management() {
        let mut ctx = Vec::new();
        let _ = type_check(&mut ctx, &Expression::IntroPoint);
        assert_eq!(*ctx, []);

        type_checks!(
            // \x: Unit -> \y: Bool -> <y, x>
            lambda(unit(), lambda(bool(), pair(var(1), var(3))))
        =>
            // Unit -> Bool -> Bool * Unit
            pi(unit(), pi(bool(), sigma(bool(), unit())))
        );
    }
}

