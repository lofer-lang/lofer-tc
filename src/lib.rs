#![allow(dead_code)]

#[derive(Clone)]
enum Expression {
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
        variable: Box<Type>,
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

#[derive(Clone, PartialEq, Debug)]
enum Type {
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
    // Universes needed for type families and hence type dependence
}

fn type_check(context: &mut Vec<Type>, expr: &Expression) -> Result<Type, ()> {
    use Expression::*;
    match *expr {
        Variable(i) => {
            Ok(context[context.len() - i].clone())
        },

        IntroPoint => {
            Ok(Type::Unit)
        },

        IntroTT | IntroFF => {
            Ok(Type::Bool)
        },
        ElimIf { ref condition, ref tt_branch, ref ff_branch } => {
            let condition_type = type_check(context, condition)?;
            if let Type::Bool = condition_type {
                let tt_check = type_check(context, tt_branch)?;
                let ff_check = type_check(context, ff_branch)?;
                if tt_check == ff_check {
                    Ok(tt_check)
                } else {
                    Err(())
                }
            } else {
                Err(())
            }
        },

        IntroLambda { ref variable, ref body } => {
            let variable_clone = (**variable).clone();
            context.push(variable_clone);
            let maybe_codomain = type_check(context, body);
            let domain = Box::new(context.pop().unwrap());
            let codomain = Box::new(maybe_codomain?);
            Ok(Type::Pi { domain, codomain })
        },
        ElimApplication { ref function, ref argument } => {
            let fun_type = type_check(context, function)?;
            let arg_type = type_check(context, argument)?;
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
            let fst_type = type_check(context, fst)?;
            context.push(fst_type);
            let maybe_snd_type = type_check(context, snd);
            let fst_type = Box::new(context.pop().unwrap());
            let snd_type = Box::new(maybe_snd_type?);
            Ok(Type::Sigma { fst_type, snd_type })
        },
        ElimFst { ref pair } => {
            let pair_type = type_check(context, pair)?;
            if let Type::Sigma { fst_type, .. } = pair_type {
                Ok(*fst_type)
            } else {
                Err(())
            }
        },
        ElimSnd { ref pair } => {
            let pair_type = type_check(context, pair)?;
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
    #[test]
    fn discrete_type_checking() {
        let mut ctx = Vec::new();
        assert_eq!(Ok(Type::Unit),
            type_check(&mut ctx, &Expression::IntroPoint));
        assert_eq!(Ok(Type::Bool), type_check(&mut ctx, &Expression::IntroTT));
        assert_eq!(Ok(Type::Bool), type_check(&mut ctx, &Expression::IntroFF));
        let branch_unit = Expression::ElimIf {
            condition: Box::new(Expression::IntroTT),
            tt_branch: Box::new(Expression::IntroPoint),
            ff_branch: Box::new(Expression::IntroPoint),
        };
        assert_eq!(Ok(Type::Unit), type_check(&mut ctx, &branch_unit));
        let branch_bad_cond = Expression::ElimIf {
            condition: Box::new(Expression::IntroPoint),
            tt_branch: Box::new(Expression::IntroTT),
            ff_branch: Box::new(Expression::IntroTT),
        };
        assert_eq!(Err(()), type_check(&mut ctx, &branch_bad_cond));
        let branch_unmatching = Expression::ElimIf {
            condition: Box::new(Expression::IntroTT),
            tt_branch: Box::new(Expression::IntroTT),
            ff_branch: Box::new(Expression::IntroPoint),
        };
        assert_eq!(Err(()), type_check(&mut ctx, &branch_unmatching));
    }

    #[test]
    fn function_type_checking() {
        let mut ctx = Vec::new();

        let expr = Expression::IntroLambda {
            variable: Box::new(Type::Unit),
            body: Box::new(Expression::Variable(1)),
        };
        let expected = Type::Pi {
            domain: Box::new(Type::Unit),
            codomain: Box::new(Type::Unit),
        };
        let actual = type_check(&mut ctx, &expr);
        assert_eq!(Ok(expected), actual);

        let expr = Expression::ElimApplication {
            function: Box::new(Expression::IntroLambda {
                variable: Box::new(Type::Bool),
                body: Box::new(Expression::IntroPoint),
            }),
            argument: Box::new(Expression::IntroTT),
        };
        let expected = Type::Unit;
        let actual = type_check(&mut ctx, &expr);
        assert_eq!(Ok(expected), actual);

        let expr = Expression::ElimApplication {
            function: Box::new(Expression::IntroLambda {
                variable: Box::new(Type::Bool),
                body: Box::new(Expression::IntroPoint),
            }),
            argument: Box::new(Expression::IntroPoint),
        };
        let expected = ();
        let actual = type_check(&mut ctx, &expr);
        assert_eq!(Err(expected), actual);

        let expr = Expression::ElimApplication {
            function: Box::new(Expression::IntroPoint),
            argument: Box::new(Expression::IntroTT),
        };
        let expected = ();
        let actual = type_check(&mut ctx, &expr);
        assert_eq!(Err(expected), actual);
    }

    #[test]
    fn pair_type_checking() {
        let mut ctx = Vec::new();

        let expr = Expression::IntroPair {
            fst: Box::new(Expression::IntroPoint),
            snd: Box::new(Expression::IntroTT),
        };
        let expected = Type::Sigma {
            fst_type: Box::new(Type::Unit),
            snd_type: Box::new(Type::Bool),
        };
        let actual = type_check(&mut ctx, &expr);
        assert_eq!(Ok(expected), actual);

        let fst = Expression::ElimFst {
            pair: Box::new(expr.clone()),
        };
        assert_eq!(Ok(Type::Unit), type_check(&mut ctx, &fst));

        let snd = Expression::ElimSnd {
            pair: Box::new(expr.clone()),
        };
        assert_eq!(Ok(Type::Bool), type_check(&mut ctx, &snd));

        let fst = Expression::ElimFst {
            pair: Box::new(Expression::IntroPoint),
        };
        assert_eq!(Err(()), type_check(&mut ctx, &fst));

        let snd = Expression::ElimSnd {
            pair: Box::new(Expression::IntroPoint),
        };
        assert_eq!(Err(()), type_check(&mut ctx, &snd));
    }

    // passes since sigma will be dependent in the future
    #[test]
    fn strange_diagonal() {
        let mut ctx = Vec::new();

        let expr = Expression::IntroPair {
            fst: Box::new(Expression::IntroTT),
            snd: Box::new(Expression::Variable(1)),
        };
        let expected = Type::Sigma {
            fst_type: Box::new(Type::Bool),
            snd_type: Box::new(Type::Bool),
        };
        let actual = type_check(&mut ctx, &expr);
        assert_eq!(Ok(expected), actual);
    }

    #[test]
    fn variable_management() {
        let mut ctx = Vec::new();
        let _ = type_check(&mut ctx, &Expression::IntroPoint);
        assert_eq!(*ctx, []);

        // \x: Unit -> \y: Bool -> <y, x>
        let expr = Expression::IntroLambda {
            variable: Box::new(Type::Unit),
            body: Box::new(Expression::IntroLambda {
                variable: Box::new(Type::Bool),
                body: Box::new(Expression::IntroPair {
                    fst: Box::new(Expression::Variable(1)),
                    snd: Box::new(Expression::Variable(3)), // since fst is in
                }),                                         // in the ctx
            }),
        };
        // Unit -> Bool -> Bool * Unit
        let expected = Type::Pi {
            domain: Box::new(Type::Unit),
            codomain: Box::new(Type::Pi {
                domain: Box::new(Type::Bool),
                codomain: Box::new(Type::Sigma {
                    fst_type: Box::new(Type::Bool),
                    snd_type: Box::new(Type::Unit),
                }),
            }),
        };
        let actual = type_check(&mut ctx, &expr);
        assert_eq!(Ok(expected), actual);
        assert_eq!(*ctx, []);
    }
}

