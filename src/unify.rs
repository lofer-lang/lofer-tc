use super::*;

pub(super) struct Meta {
    solution: Option<Expr>,
    ty: Expr,
    // @Performance flatten, @Performance bitset, @Performance alloca
    dependencies: Vec<bool>,
}

pub(super) fn meta(metas: &mut Vec<Meta>, ty: Expr) -> Expr {
    metas.push(Meta { solution: None, ty, dependencies: Vec::new() });
    Expr {
        arrow_params: Vec::new(),
        head: Ident::Meta(metas.len() - 1),
        tail: Vec::new()
    }
}

fn unify(metas: &mut Vec<Meta>, mut lhs: Expr, mut rhs: Expr) -> Result<(), ()> {
    let mut lhs_var = None;
    loop {
        if let Some(i) = lhs.meta_ident() {
            lhs_var = Some(i);
            if let Some(x) = metas[i].solution.clone() {
                lhs = x;
                continue;
            }
        }
        if let Some(i) = rhs.meta_ident() {
            // _n = _n always unifies without adding any information
            if lhs_var == Some(i) {
                return Ok(());
            }
            if let Some(x) = metas[i].solution.clone() {
                rhs = x;
                continue;
            }
        }
        lhs_var = None;

        if let Some(i) = lhs.meta_ident() {
            return check_solution(metas, i, rhs);
        }
        if let Some(i) = rhs.meta_ident() {
            return check_solution(metas, i, lhs);
        }

        if lhs.arrow_params.len() > 0 && rhs.arrow_params.len() > 0 {
            unify(metas, lhs.arrow_params.remove(0), rhs.arrow_params.remove(0))?;
            continue;
        }
        if lhs.arrow_params.len() > 0 || rhs.arrow_params.len() > 0 {
            return Err(());
        }

        if lhs.tail.len() > 0 && rhs.tail.len() > 0 {
            unify(metas, lhs.tail.pop().unwrap(), rhs.tail.pop().unwrap())?;
            continue;
        }
        if lhs != rhs {
            return Err(());
        }

        return Ok(());
    }
}

fn check_deps(metas: &Vec<Meta>, deps: &mut Vec<bool>, sol: &Expr) {
    for x in &sol.arrow_params {
        check_deps(metas, deps, x);
    }
    for x in &sol.tail {
        check_deps(metas, deps, x);
    }
    if let Ident::Meta(i) = sol.head {
        // @Performance if deps[i] { return; } // short circuit condition should hold
        deps[i] = true;
        for j in 0..metas[i].dependencies.len() {
            deps[j] |= metas[i].dependencies[j];
        }
    }
}

fn check_solution(metas: &mut Vec<Meta>, i: usize, sol: Expr) -> Result<(), ()> {
    let mut deps = Vec::new();
    deps.resize(metas.len(), false);
    check_deps(metas, &mut deps, &sol);
    let cyclic: bool = deps[i];
    metas[i].dependencies = deps;
    metas[i].solution = Some(sol);
    if cyclic {
        Err(())
    } else {
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    //use *;
    use unify::*;
    #[test]
    fn basic_unify() {
        let ref mut metas = Vec::new();
        let x = meta(metas, Expr::universe(1));
        unify(metas, x.clone(), x.clone()).unwrap();
        unify(metas, x.clone(), Expr::universe(0)).unwrap();
        unify(metas, x.clone(), Expr::universe(0)).unwrap();
        unify(metas, x.clone(), Expr::universe(1)).unwrap_err();
        if metas[0].solution != Some(Expr::universe(0)) {
            panic!("Did not write meta variable");
        }
    }

    #[test]
    fn cycle() {
        let ref mut metas = Vec::new();
        let x = meta(metas, Expr::universe(1));
        let y = meta(metas, Expr::universe(1));
        let mut t1 = Expr::universe(0);
        t1.arrow_params.push(y.clone());
        unify(metas, x.clone(), t1).unwrap();
        assert_eq!(metas[0].dependencies, vec![false, true]);
        let mut t2 = Expr::universe(0);
        t2.arrow_params.push(x.clone());
        unify(metas, y.clone(), t2).unwrap_err();
        assert_eq!(metas[1].dependencies, vec![true, true]);
    }
}

