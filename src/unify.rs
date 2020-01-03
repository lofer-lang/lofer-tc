use super::*;

pub(super) struct Meta {
    solution: Option<Expr>,
    // @Performance flatten, @Performance bitset, @Performance alloca
    dependencies: Vec<bool>,
    type_constraints: Vec<(u32, Expr)>,
}

pub(super) fn meta(metas: &mut Vec<Meta>) -> Expr {
    let meta = Meta {
        solution: None,
        dependencies: Vec::new(),
        type_constraints: Vec::new(),
    };
    let id = metas.len();
    metas.push(meta);
    Expr {
        arrow_params: Vec::new(),
        head: Ident::Meta(id, 0),
        tail: Vec::new()
    }
}

// @Performance &Expr?
pub(super) fn unify(metas: &mut Vec<Meta>, mut lhs: Expr, mut rhs: Expr)
    -> Result<(), ()>
{
    let mut lhs_var = None;
    loop {
        if let Ident::Meta(i, 0) = lhs.head {
            lhs_var = Some(i);
            if let Some(x) = metas[i].solution.clone() {
                lhs = x;
                continue;
            }
        }
        if let Ident::Meta(i, 0) = rhs.head {
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

        if let Ident::Meta(i, n) = lhs.head {
            return check_solution(metas, i, n, rhs);
        }
        if let Ident::Meta(i, n) = rhs.head {
            return check_solution(metas, i, n, lhs);
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
    if let Ident::Meta(i, _n) = sol.head {
        // @Performance if deps[i] { return; } // short circuit condition should hold
        deps[i] = true;
        for j in 0..metas[i].dependencies.len() {
            deps[j] |= metas[i].dependencies[j];
        }
    }
}

fn check_solution(metas: &mut Vec<Meta>, i: usize, n: u32, sol: Expr) -> Result<(), ()> {
    if n != 0 {
        metas[i].type_constraints.push((n, sol));
        return Ok(());
    }
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
        let x = meta(metas);
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
        let x = meta(metas);
        let y = meta(metas);
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

