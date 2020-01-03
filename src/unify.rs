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

pub(super) struct MetaSolution {
    pub val: Expr,
    pub ty: Expr,
    pub level: u32,
}

pub(super) fn link_solution(globals: &Vec<Item>, locals: &Context<Expr>, metas: Vec<Meta>)
    -> Result<Vec<MetaSolution>, ()>
{
    let mut solution = Vec::with_capacity(metas.len());
    for i in 0..metas.len() {
        solution.push(MetaSolution {
            val: Expr::ident(Ident::Meta(i, 0)),
            ty: Expr::ident(Ident::Meta(i, 1)),
            level: u32::max_value(),
        });
    }
    let mut solved = Vec::new();
    solved.resize(metas.len(), false);
    let mut solved_count = 0;
    while solved_count < metas.len() {
        let mut next = None;
        for i in 0..metas.len() {
            let mut ready = true;
            for j in 0..metas.len() {
                if !solved[j] && metas[i].dependencies[j] {
                    ready = false;
                    break;
                }
            }
            if ready {
                next = Some(i);
                break;
            }
        }
        if next.is_none() {
            return Err(());
        }
        let i = next.unwrap();
        let new_sol = subst_metas(&metas[i].solution.as_ref().unwrap(), 0, 0,
            &solution, 0);
        solution[i].ty = calculate_type(globals, &mut Vec::new(), locals, &new_sol);
        solution[i].val = new_sol;

        solved_count += 1;
    }
    for i in 0..metas.len() {
        for &(n, ref val) in &metas[i].type_constraints {
            if n == 0 {
                panic!("Type constraint on actual value?");
            }
            if n > 1 {
                unimplemented!();
            }
            let expected = subst_metas(val, 0, 0, &solution, 0);
            if expected != solution[i].ty {
                return Err(());
            }
        }
    }
    Ok(solution)
}

