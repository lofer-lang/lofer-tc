#[macro_use]
extern crate lalrpop_util;

pub mod ast;
mod indent_parser;
mod eval;
mod unify;

// why am I even using lalrpop for such a simple grammar
// f : (x1: A) -> (x2: B) -> (x3: C) -> D
// f x1 x2 x3 = a (b c (d e) f) g h
lalrpop_mod!(line_parser);

pub use indent_parser::ProgramParser;

use eval::*;

struct Item {
    ty: Expr,
    def: Option<(usize, Expr)>,
}

pub struct Globals {
    names: Vec<String>,
    defs: Vec<Item>,
}

impl Globals {
    pub fn new() -> Globals {
        Globals { names: Vec::new(), defs: Vec::new() }
    }
}

pub fn type_check_all(globals: &mut Globals, programs: Vec<ast::Item>) {
    for item in &programs {
        let (name, item) = type_check_function(globals, item);
        println!("{}: {}", name, item.ty);
        globals.names.push(name);
        globals.defs.push(item);
    }

    print!("Successfully type-checked all items!\n\n");
}

fn type_check_function(
    globals: &Globals,
    fun: &ast::Item,
) -> (String, Item) {
    for _ in &fun.associated {
        unimplemented!();
    }
    if fun.annotation.is_none() {
        if fun.definition.is_none() {
            panic!("Found neither annotation nor definition?");
        } else if fun.definition.as_ref().unwrap().vars.len() > 0 {
            panic!("Terms with parameters must have a type annotation");
        } else {
            unimplemented!();
        }
    }
    let annotation = fun.annotation.as_ref().unwrap();
    let mut metas = Vec::new();
    let mut ty = convert_expr(
        &globals.names,
        &mut metas,
        &Default::default(),
        annotation.typ.clone()
    );
    sort_check_expr(&globals.defs, &mut metas, &Context::new(&[]), &ty);
    // maybe we want to store both eval and non-eval versions?
    eval(&globals.defs, &mut ty, 0);

    if fun.definition.is_none() {
        if !annotation.is_post {
            panic!("Item {} has no definition", annotation.name);
        }
        (annotation.name.clone(), Item { ty, def: None })
    } else {
        let definition = fun.definition.as_ref().unwrap();
        if annotation.name != definition.fname {
            panic!(
                "Annotation for {} was given alongside definition for {}",
                annotation.name,
                definition.fname,
            );
        }
        let var_names = &definition.vars;
        let param_num = var_names.len();

        let def = convert_expr(
            &globals.names,
            &mut metas,
            &Context::new(&var_names),
            definition.body.clone(),
        );

        if !annotation.is_post {
            let mut result = ty.clone();
            let bindings: Vec<_> = result
                .arrow_params
                .drain(0..param_num)
                .collect();

            type_check_expr(&globals.defs, &mut metas, &Context::new(&bindings), &def, &result);
        }

        let sol = unify::link_solution(
            &globals.defs,
            &Context::new(&[]),
            metas,
        ).unwrap();
        for i in 0..sol.len() {
            print!("_{}: {} = {}\n  ", i, &sol[i].ty, &sol[i].val);
        }
        let ty = subst_metas(&ty, 0, 0, &sol, 0);
        let def = subst_metas(&def, 0, 0, &sol, 0);

        (definition.fname.clone(), Item { ty, def: Some((param_num, def)) })
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Ident {
    Universe(u32),
    Global(usize),
    Local(usize),
    Meta(usize, u32),
}

#[derive(Clone, PartialEq)]
struct Expr {
    arrow_params: Vec<Expr>,
    head: Ident,
    tail: Vec<Expr>,
}

impl Expr {
    fn ident(head: Ident) -> Expr {
        Expr { arrow_params: Vec::new(), head, tail: Vec::new() }
    }
    fn universe_level(self: &Self) -> Option<u32> {
        if self.arrow_params.len() > 0 || self.tail.len() > 0 {
            None
        } else {
            match self.head {
                Ident::Universe(l) => Some(l),
                _ => None,
            }
        }
    }

    fn insert(self: &mut Self, mut other: Self) {
        if (other.universe_level().is_some() || other.arrow_params.len() > 0)
            && self.tail.len() > 0
        {
            panic!("Substituted arrow expression into head position");
        }
        self.arrow_params.append(&mut other.arrow_params);
        self.head = other.head;
        // @Performance reverse all tail arrays
        // specifically to make this faster
        other.tail.append(&mut self.tail);
        self.tail = other.tail;
    }

    fn write_grouped(
        self: &Self,
        f: &mut std::fmt::Formatter,
        group_algs: bool,
    ) -> std::fmt::Result {
        if self.arrow_params.len() > 0 || (group_algs && self.tail.len() > 0) {
            write!(f, "({})", self)?;
        } else {
            write!(f, "{}", self)?;
        }
        Ok(())
    }
}

impl std::fmt::Display for Expr {
    fn fmt(self: &Self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        for ex in &self.arrow_params {
            ex.write_grouped(f, false)?;
            write!(f, " -> ")?;
        }
        match self.head {
            Ident::Universe(l) => {
                write!(f, "U{}", l)?;
            },
            Ident::Local(i) => {
                write!(f, "x{}", i)?;
            },
            Ident::Global(i) => {
                write!(f, "g{}", i)?;
            },
            Ident::Meta(i, n) => {
                write!(f, "_{}", i)?;
                if n > 0 {
                    write!(f, "_")?;
                    for _ in 0..n {
                        write!(f, "t")?;
                    }
                }
            },
        }
        for ex in &self.tail {
            write!(f, " ")?;
            ex.write_grouped(f, true)?;
        }
        Ok(())
    }
}

#[derive(Default)]
struct Context<'a, T> {
    prev_size: usize,
    prev: Option<&'a Context<'a, T>>,
    this: &'a [T],
}

impl<'a, T> Context<'a, T> {
    fn new(this: &'a [T]) -> Self {
        Context { this, prev_size: 0, prev: None }
    }
    fn push(self: &'a Self, next: &'a [T]) -> Self {
        // this doesn't actually shadow anything because of the size we use
        self.push_shadowed(next, self.size())
    }
    // shadows indeces, cannot be used with shadowed names
    // (maybe I should stop calling one of these shadowing...)
    fn push_shadowed(self: &'a Self, next: &'a [T], unshadowed: usize) -> Self {
        Context {
            prev_size: unshadowed,
            prev: Some(self),
            this: next,
        }
    }
    fn size(self: &Self) -> usize {
        self.prev_size + self.this.len()
    }

    // NOT valid on expressions with shadowed indeces
    // this is so that we can efficiently implement shadowed _parameter names_
    fn index_from_value(self: &Self, name: &T) -> Option<usize>
        where T: PartialEq,
    {
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
    fn value_from_index(self: &'a Self, index: usize) -> &'a T {
        let mut curr = self;
        loop {
            if index < curr.prev_size {
                curr = curr.prev.expect("Nonzero prev_size but no prev??");
            } else {
                return &curr.this[index - curr.prev_size];
            }
        }
    }
}

fn get_index<T: PartialEq>(names: &[T], name: &T) -> Option<usize> {
    let mut result = names.len();
    while result > 0 {
        result -= 1;
        if names[result] == *name {
            return Some(result);
        }
    }
    None
}

fn convert_expr(
    globals: &Vec<String>,
    metas: &mut Vec<unify::Meta>,
    locals: &Context<String>,
    mut expr: ast::Expr,
) -> Expr {
    let mut arrow_params = Vec::new();
    let mut new_locals = Vec::new();
    while let ast::Expr::Arrow(ast::ArrowExpr { params, output }) = expr {
        for (name, ty) in params {
            arrow_params.push(
                convert_expr(globals, metas, &locals.push(&new_locals), ty)
            );
            new_locals.push(name.unwrap_or_else(|| "_".into()));
        }
        expr = *output;
    }
    let locals = locals.push(&new_locals);
    let alg = match expr {
        ast::Expr::Arrow(_) => unreachable!(),
        ast::Expr::Alg(alg) => alg,
    };

    let head = {
        if alg.head == "_" {
            unify::meta(metas).head
        } else if let Some(id) = locals.index_from_value(&alg.head) {
            Ident::Local(id)
        } else if let Some(id) = get_index(globals, &alg.head) {
            Ident::Global(id)
        } else {
            if &alg.head[..1] != "U" {
                panic!("Could not find term for identifier: {}", alg.head);
            }
            if let Ok(l) = alg.head[1..].parse() {
                Ident::Universe(l)
            } else {
                panic!("Could not find term for identifier: {}", alg.head);
            }
        }
    };
    let tail = alg
        .tail
        .into_iter()
        .map(|ex| convert_expr(globals, metas, &locals, ex))
        .collect();
    Expr { arrow_params, head, tail }
}

fn calculate_type(
    globals: &Vec<Item>,
    metas: &mut Vec<unify::Meta>,
    locals: &Context<Expr>,
    expr: &Expr,
) -> Expr {
    // process variables introduced by arrow expressions
    let mut new_locals = Vec::new();
    for each in &expr.arrow_params {
        sort_check_expr(
            globals,
            metas,
            &locals.push(&new_locals),
            each,
        );
        new_locals.push(each.clone());
    }
    let locals = locals.push(&new_locals);
    // initialize with type of term in head position
    let (mut actual, mut expr_ctx_size) = match expr.head {
        Ident::Local(i) => (locals.value_from_index(i).clone(), i),
        Ident::Global(i) => (globals[i].ty.clone(), 0),
        Ident::Universe(l) => {
            if expr.tail.len() > 0 {
                panic!("Cannot apply type to arguments");
            }
            return Expr::ident(Ident::Universe(l+1));
        },
        Ident::Meta(i, n) => {
            if n != 0 {
                println!("Had to find type of type of a metavariable!");
            }
            (Expr {
                arrow_params: Vec::new(),
                head: Ident::Meta(i, n+1),
                tail: Vec::new(),
            }, locals.size())
        },
    };
    // check that arguments match the type expected in head position
    let mut checked = 0;
    let mut subbed = 0;
    while checked < expr.tail.len() {
        if actual.arrow_params.len() == 0 {
            // @Performance lazy eval? save the full eval for later
            actual = subst(
                &actual, expr_ctx_size, 0,
                &expr.tail[subbed..checked], locals.size(),
            );
            subbed = checked;
            expr_ctx_size = locals.size();
            eval(globals, &mut actual, locals.size());
            if actual.arrow_params.len() == 0 {
                panic!("Cannot apply type family to argument(s): {}",
                       actual);
            }
        }
        // the first parameter of the actual type is the expected type for
        // the first argument
        let arg_expected_base = actual.arrow_params.remove(0);

        // @Memory maybe subst could take &mut param?
        // @Performance skip this cloning operation if i is 0?
        let mut arg_expected = subst(
            &arg_expected_base, expr_ctx_size, 0,
            &expr.tail[subbed..checked], locals.size(),
        );
        // @Performance that's a lot of eval
        eval(globals, &mut arg_expected, locals.size());
        type_check_expr(
            globals,
            metas,
            &locals,
            &expr.tail[checked],
            &arg_expected,
        );
        checked += 1;
    }

    // return result of applying head to all given arguments
    actual = subst(
        &actual, expr_ctx_size, 0,
        &expr.tail[subbed..checked], locals.size(),
    );
    eval(globals, &mut actual, locals.size());
    if expr.arrow_params.len() > 0 && actual.universe_level().is_none() {
        panic!("Expected element of a universe (in result of arrow expression)");
    }
    return actual;
}

fn sort_check_expr(
    globals: &Vec<Item>,
    metas: &mut Vec<unify::Meta>,
    locals: &Context<Expr>,
    expr: &Expr,
) -> u32 {
    let actual = calculate_type(globals, metas, locals, expr);
    if let Some(l) = actual.universe_level() {
        l
    } else {
        panic!("Expected element of a universe");
    }
}

fn type_check_expr(
    globals: &Vec<Item>,
    metas: &mut Vec<unify::Meta>,
    locals: &Context<Expr>,
    expr: &Expr,
    expected: &Expr,
) {
    let actual = calculate_type(globals, metas, locals, expr);
    assert_type(metas, expr, &actual, expected);
}


fn assert_type(metas: &mut Vec<unify::Meta>, expr: &Expr, actual: &Expr, expected: &Expr) {
    if unify::unify(metas, actual.clone(), expected.clone()).is_err() {
        panic!("\n\n{} has type:\n  {}\n\nbut it was expected to have type:\n  {}\n\n",
               expr, actual, expected);
    }
}

