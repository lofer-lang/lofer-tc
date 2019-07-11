#[macro_use]
extern crate lalrpop_util;

pub mod ast;
mod indent_parser;

// why am I even using lalrpop for such a simple grammar
// f : (x1: A) -> (x2: B) -> (x3: C) -> D
// f x1 x2 x3 = a (b c (d e) f) g h
lalrpop_mod!(line_parser);

pub use indent_parser::ProgramParser;

pub fn type_check_all(programs: Vec<ast::Item>) {
    let mut global_names = Vec::with_capacity(programs.len());
    let mut globals = Vec::with_capacity(programs.len());
    for item in &programs {
        let (name, ty) = type_check_function(&global_names, &globals, item);
        println!("Success: {}", name);
        global_names.push(name);
        globals.push(ty);
    }
}

fn type_check_function(
    global_names: &Vec<String>,
    globals: &Vec<Expr>,
    fun: &ast::Item,
) -> (String, Expr) {
    for _ in &fun.associated {
        unimplemented!();
    }
    if fun.annotation.is_none() {
        if fun.definition.vars.len() > 0 {
            panic!("Terms with parameters must have a type annotation");
        } else {
            unimplemented!();
        }
    }
    let annotation = fun.annotation.as_ref().unwrap();
    if annotation.name != fun.definition.fname {
        panic!(
            "Annotation for {} was given alongside definition for {}",
            annotation.name,
            fun.definition.fname,
        );
    }
    let var_names = &fun.definition.vars;
    let annotation = convert_expr(
        global_names,
        &Default::default(),
        annotation.typ.clone()
    );
    let (bindings, result) =
        split_ctx_output(annotation.clone(), fun.definition.vars.len());
    let ctx = NameChain::with_names(var_names.clone());
    let body = convert_expr(
        global_names,
        &ctx,
        fun.definition.body.clone()
    );

    type_check_expr(globals, &bindings, &body, &result);
    (fun.definition.fname.clone(), annotation)
}

// @Completeness need to manually implement our own comparison (instead of PartialEq)
// since Arrows with different unshadowed values may be equivalent
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Ident {
    //Postulate(usize),
    Global(usize),
    Local(usize),
}

#[derive(Clone, PartialEq, Debug)]
enum Expr {
    Type,
    Arrow { unshadowed: usize, ends: Vec<Expr> },
    Alg { head: Ident, tail: Vec<Expr> },
}

type Context = Vec<Expr>;

#[derive(Default)]
struct NameChain<'a> {
    prev_size: usize,
    prev: Option<&'a NameChain<'a>>,
    this: Vec<String>,
}

impl<'a> NameChain<'a> {
    fn with_names(this: Vec<String>) -> Self {
        NameChain { this, ..Default::default() }
    }
    fn push(self: &'a Self) -> Self {
        NameChain {
            prev_size: self.size(),
            prev: Some(self),
            this: Vec::new(),
        }
    }
    fn size(self: &Self) -> usize {
        self.prev_size + self.this.len()
    }

    fn get_index(self: &Self, name: &str) -> Option<usize> {
        let mut curr = self;
        loop {
            if let Some(result) = get_index(&curr.this, name) {
                return Some(result + curr.prev_size);
            }
            if let Some(prev) = &curr.prev {
                curr = prev;
            } else {
                return None;
            }
        }
    }
}

fn get_index(names: &Vec<String>, name: &str) -> Option<usize> {
    let mut result = names.len();
    while result > 0 {
        result -= 1;
        if names[result] == name {
            return Some(result);
        }
    }
    None
}

fn convert_expr(
    globals: &Vec<String>,
    locals: &NameChain,
    expr: ast::Expr,
) -> Expr {
    match expr {
        ast::Expr::Arrow(ast::ArrowExpr { params, output }) => {
            let mut ends = Vec::new();
            let mut locals = locals.push();
            for (name, ty) in params {
                ends.push(convert_expr(globals, &locals, ty));
                locals.this.push(name.unwrap_or("_".into()));
            }
            // TODO detect arrow to arrow and merge
            ends.push(convert_expr(globals, &locals, *output));
            Expr::Arrow { unshadowed: locals.size(), ends }
        },
        ast::Expr::Alg(ast::AlgExpr { head, tail }) => {
            let head = {
                if let Some(id) = locals.get_index(&head) {
                    Ident::Local(id)
                } else if let Some(id) = get_index(globals, &head) {
                    Ident::Global(id)
                } else if head == "Type" {
                    if tail.len() > 0 {
                        panic!("cannot apply term `Type` of type `Type` to arguments");
                    } else {
                        return Expr::Type;
                    }
                } else {
                    panic!("Could not find term for identifier: {}", head);
                }
            };
            let tail = tail
                .into_iter()
                .map(|ex| convert_expr(globals, locals, ex))
                .collect();
            // TODO test whether function needs to be evaluated
            Expr::Alg { head, tail }
        },
    }
}

fn split_ctx_output_vec(mut ctx: Vec<Expr>, n: usize) -> (Context, Expr) {
    if ctx.len() > n + 1 {
        let terms = ctx.drain(n..).collect();
        (ctx, Expr::Arrow { unshadowed: n, ends: terms })
    } else if ctx.len() == n + 1 {
        let output = ctx.pop().unwrap();
        (ctx, output)
    } else { // ctx.len() < n + 1
        panic!("Too many parameters for given annotation");
    }
}

fn split_ctx_output(expr: Expr, n: usize) -> (Context, Expr) {
    if let Expr::Arrow { ends, .. } = expr {
        split_ctx_output_vec(ends, n)
    } else {
        if n == 0 {
            (Vec::new(), expr)
        } else {
            panic!("Too many parameters for given annotation. (not expecting any)");
        }
    }
}

fn type_check_expr(
    globals: &Vec<Expr>,
    locals: &Context,
    expr: &Expr,
    expected: &Expr,
) {
    let actual = determine_type(globals, locals, expr);
    // @Completeness evaluate actual and expected first?
    if actual != *expected {
        panic!("Types did not match\n\nexpected: {:?}\n\ngot: {:?}", expected, actual);
    }
}

// figures out the type of an expression,
// while also checking that function applications are valid
fn determine_type(
    globals: &Vec<Expr>,
    locals: &Context,
    expr: &Expr,
) -> Expr {
    match expr {
        Expr::Type => Expr::Type,
        Expr::Arrow { ends, .. } => {
            for each in ends {
                type_check_expr(globals, locals, each, &Expr::Type);
            }
            Expr::Type
        },
        Expr::Alg{head, tail} => {
            let mut checked = 0;
            let (mut expr_ty, expr_ctx_size) = match *head {
                Ident::Local(i) => (locals[i].clone(), i),
                Ident::Global(i) => (globals[i].clone(), 0),
            };
            while checked < tail.len() {
                match expr_ty {
                    Expr::Arrow { ends, .. } => {
                        while checked < tail.len() && checked < ends.len() - 1 {
                            // @Memory maybe subst could take &mut param?
                            // @Performance skip this cloning operation if i is 0?
                            let param_ty = subst(
                                &ends[checked], expr_ctx_size,
                                &tail[0..checked], locals.len(),
                            );
                            type_check_expr(
                                globals,
                                locals,
                                &tail[checked],
                                &param_ty,
                            );
                            checked += 1;
                        }
                        if checked < ends.len() - 1 {
                            expr_ty = Expr::Arrow {
                                unshadowed: expr_ctx_size + checked,
                                ends: ends[checked..].to_owned()
                            };
                        } else { // checked == ends.len() - 1
                            expr_ty = {ends}.pop().unwrap();
                        }
                        expr_ty = subst(
                            &expr_ty, expr_ctx_size,
                            &tail[0..checked], locals.len(),
                        );
                    },
                    Expr::Alg { head, tail } => {
                        // attempt to reduce and if it can't be reduced complain
                        unimplemented!();
                    },
                    Expr::Type => {
                        panic!("Cannot apply type to arguments");
                    },
                }
            }
            expr_ty
        },
    }
}

// takes an expression M valid in G1, (a + m + e variables)
// and a set of arguments X1..Xm valid in G2 (n variables) where a <= n
// then generates an expression M[x(a+i) <- Xi, x(a+m+i) <- x(n+i)]
fn subst(
    base: &Expr, base_ctx_size: usize,
    args: &[Expr], arg_ctx_size: usize,
) -> Expr {
    match base {
        Expr::Type => Expr::Type,
        &Expr::Arrow { unshadowed, ref ends } => {
            // what on earth am I doing here
            let new_args = {
                if unshadowed <= base_ctx_size {
                    // ignore arguments... does subst do anything?
                    0
                } else if unshadowed <= base_ctx_size + args.len() {
                    // substitute some arguments
                    unshadowed - base_ctx_size
                } else {
                    // substitute all arguments and add some 
                    args.len()
                }
            };
            let mut new_ends = Vec::with_capacity(ends.len());
            for end in ends.iter() {
                // I love non-relative indexing
                // the extra variables generated
                // by iterating through these parameters
                // are handled by the third branch
                // in the Local(i) code below
                new_ends.push(subst(end, base_ctx_size,
                                    &args[0..new_args], arg_ctx_size));
            }
            Expr::Arrow { unshadowed: arg_ctx_size, ends: new_ends }
        },
        Expr::Alg { head, tail } => {
            let new_head;
            let mut new_tail = Vec::new();
            match *head {
                Ident::Local(i) => {
                    if i < base_ctx_size {
                        new_head =  Ident::Local(i);
                    } else if i - base_ctx_size < args.len() {
                        let result = args[i - base_ctx_size].clone();
                        if let Expr::Alg { head, tail } = result {
                            new_head = head;
                            new_tail = tail;
                        } else if tail.len() == 0 {
                            return result;
                        } else {
                            panic!("Substituted builtin type into head position... cannot apply type to arguments");
                        }
                    } else {
                        let e = i - (base_ctx_size + args.len());
                        new_head = Ident::Local(arg_ctx_size + e);
                    }
                },
                _ => new_head = *head,
            }
            new_tail.reserve(tail.len());
            for expr in tail {
                new_tail.push(subst(expr, base_ctx_size,
                                    args, arg_ctx_size));
            }
            Expr::Alg { head: new_head, tail: new_tail }
        },
    }
}
