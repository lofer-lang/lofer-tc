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
        let (name, item) = type_check_function(&global_names, &globals, item);
        println!("{}: {}", name, item.ty);
        global_names.push(name);
        globals.push(item);
    }

    println!("\nSuccessfully type-checked all items!");
}

struct Item {
    ty: Expr,
    param_num: usize,
    def: Expr,
}

fn type_check_function(
    global_names: &Vec<String>,
    globals: &Vec<Item>,
    fun: &ast::Item,
) -> (String, Item) {
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
    let param_num = var_names.len();
    // convert annotation
    let mut ty = convert_expr(
        global_names,
        &Default::default(),
        annotation.typ.clone()
    );
    eval(globals, &mut ty, 0);
    // pull param types
    let mut result = ty.clone();
    let bindings: Vec<_> = result
        .arrow_params
        .drain(0..param_num)
        .collect();
    // convert definition
    let def = convert_expr(
        global_names,
        &Context::new(&var_names),
        fun.definition.body.clone(),
    );

    // check definition has the right type
    type_check_expr(globals, &Context::new(&bindings), &def, result);
    (fun.definition.fname.clone(), Item { ty, param_num, def })
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Ident {
    //Postulate(usize),
    Type, // Postulate(0)? Postulate(~0)?
    Global(usize),
    Local(usize),
}

#[derive(Clone, PartialEq)]
struct Expr {
    arrow_params: Vec<Expr>,
    head: Ident,
    tail: Vec<Expr>,
}

impl Expr {
    fn universe() -> Self {
        Expr {
            arrow_params: Vec::new(),
            head: Ident::Type,
            tail: Vec::new(),
        }
    }
    fn is_universe(self: &Self) -> bool {
        *self == Expr::universe()
    }
    fn write_grouped(self: &Self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        if self.arrow_params.len() > 0 || self.tail.len() > 0 {
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
            ex.write_grouped(f)?;
            write!(f, " -> ")?;
        }
        match self.head {
            Ident::Type => {
                write!(f, "Type")?;
            },
            Ident::Local(i) => {
                write!(f, "x{}", i)?;
            },
            Ident::Global(i) => {
                write!(f, "g{}", i)?;
            },
        }
        for ex in &self.tail {
            write!(f, " ")?;
            ex.write_grouped(f)?;
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
    locals: &Context<String>,
    mut expr: ast::Expr,
) -> Expr {
    let mut arrow_params = Vec::new();
    let mut new_locals = Vec::new();
    while let ast::Expr::Arrow(ast::ArrowExpr { params, output }) = expr {
        for (name, ty) in params {
            arrow_params.push(
                convert_expr(globals, &locals.push(&new_locals), ty)
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
        if let Some(id) = locals.index_from_value(&alg.head) {
            Ident::Local(id)
        } else if let Some(id) = get_index(globals, &alg.head) {
            Ident::Global(id)
        } else if alg.head == "Type" {
            Ident::Type
        } else {
            panic!("Could not find term for identifier: {}", alg.head);
        }
    };
    let tail = alg
        .tail
        .into_iter()
        .map(|ex| convert_expr(globals, &locals, ex))
        .collect();
    Expr { arrow_params, head, tail }
}

fn type_check_expr(
    globals: &Vec<Item>,
    locals: &Context<Expr>,
    expr: &Expr,
    expected: Expr,
) {
    let mut new_locals = Vec::new();
    if expr.arrow_params.len() > 0 {
        // @Performance @Memory maybe Context<&Expr>??
        for each in &expr.arrow_params {
            type_check_expr(
                globals,
                &locals.push(&new_locals),
                each,
                Expr::universe(),
            );
            new_locals.push(each.clone());
        }
        // doesn't just check that the arrow expression was meant to be a type
        // the result expression also needs to be a type,
        // so we are implicitly assigning `expected = universe();`
        if !expected.is_universe() {
            panic!("Expected {}, got Type", expected);
        }
    }
    let locals = locals.push(&new_locals);
    let mut checked = 0;
    let (mut actual_base, expr_ctx_size) = match expr.head {
        Ident::Local(i) => (locals.value_from_index(i).clone(), i),
        Ident::Global(i) => (globals[i].ty.clone(), 0),
        Ident::Type => {
            if expr.tail.len() > 0 {
                panic!("Cannot apply type to arguments");
            }
            return;
        },
    };
    while checked < expr.tail.len() {
        if actual_base.arrow_params.len() == 0 {
            // @Performance lazy eval? save the full eval for later
            eval(globals, &mut actual_base, locals.size());
            if actual_base.arrow_params.len() == 0 {
                panic!("Cannot apply type family to argument(s): {}",
                       actual_base);
            }
        }
        // the first parameter of the actual type is
        // the expected type for the first argument
        let arg_expected_base = actual_base.arrow_params.remove(0);

        // @Memory maybe subst could take &mut param?
        // @Performance skip this cloning operation if i is 0?
        let arg_expected = subst(
            &arg_expected_base, expr_ctx_size, 0,
            &expr.tail[0..checked], locals.size(),
        );
        type_check_expr(
            globals,
            &locals,
            &expr.tail[checked],
            arg_expected,
        );
        checked += 1;
    }

    let mut actual = subst(
        &actual_base, expr_ctx_size, 0,
        &expr.tail[0..checked], locals.size(),
    );
    eval(globals, &mut actual, locals.size());
    if actual != expected {
        panic!("Types did not match\n\nexpected: {}\n\ngot: {}", expected, actual);
    }
}

fn eval_on(globals: &Vec<Item>, xs: &mut Vec<Expr>, ctx_size: &mut usize, incr: bool) {
    for x in xs {
        eval(globals, x, *ctx_size);
        if incr {
            *ctx_size += 1;
        }
    }
}

fn eval(globals: &Vec<Item>, expr: &mut Expr, mut ctx_size: usize) {
    eval_on(globals, &mut expr.arrow_params, &mut ctx_size, true);
    eval_on(globals, &mut expr.tail, &mut ctx_size, false);

    while let Ident::Global(i) = expr.head {
        let param_num = globals[i].param_num;
        if expr.tail.len() >= param_num {
            let mut result = subst(
                &globals[i].def, 0, 0,
                &expr.tail[0..param_num], ctx_size,
            );
            // recurse... often redundant... @Performance? combine with subst?
            // type checking should prevent associativity problems
            // A -> (B -> x y z) w
            eval_on(globals, &mut result.arrow_params, &mut ctx_size, true);
            eval_on(globals, &mut result.tail, &mut ctx_size, false);
            expr.arrow_params.append(&mut result.arrow_params);
            expr.head = result.head;
            // @Performance we are allocating again every time...
            // could just combine these steps or something more tricky
            expr.tail.drain(0..param_num);
            result.tail.append(&mut expr.tail);
            expr.tail = result.tail;
        } else {
            break;
        }
    }
}

// takes an expression M valid in G1, (s + m + e variables)
// and a set of arguments X1..Xm valid in G2 (n variables) where s <= n
// then generates an expression M[x(s+i) <- Xi, x(s+m+i) <- x(n+i)]
// but with Xi[x(n+i) <- x(n+e+i)] in each substitution,
// in cases where arrow expressions are substituted _into_ arrow expressions
fn subst(
    base: &Expr, shared_ctx_size: usize, mut extra_ctx_size: usize,
    args: &[Expr], arg_ctx_size: usize,
) -> Expr {
    let mut arrow_params = Vec::with_capacity(base.arrow_params.len());
    for ex in &base.arrow_params {
        arrow_params.push(
             subst(ex, shared_ctx_size, extra_ctx_size, args, arg_ctx_size)
        );
        extra_ctx_size += 1;
    }
    let mut tail = Vec::with_capacity(base.tail.len());
    for ex in &base.tail {
        tail.push(
             subst(ex, shared_ctx_size, extra_ctx_size, args, arg_ctx_size)
        );
    }
    let head;
    match base.head {
        Ident::Local(i) => {
            if i < shared_ctx_size {
                head =  Ident::Local(i);
            } else if i - shared_ctx_size < args.len() {
                // @Correctness @Completeness deepen this first
                let mut result = deepen(
                    &args[i - shared_ctx_size],
                    arg_ctx_size,
                    extra_ctx_size,
                );
                arrow_params.append(&mut result.arrow_params);
                head = result.head;
                // @Performance combine these like in eval
                // does Vec::prepend exist?
                // actually we should probably just reverse argument lists
                result.tail.append(&mut tail);
                tail = result.tail;
            } else {
                let e = i - (shared_ctx_size + args.len());
                head = Ident::Local(arg_ctx_size + e);
            }
        },
        _ => head = base.head,
    }
    Expr { arrow_params, head, tail }
}

fn deepen(arg: &Expr, arg_ctx_size: usize, extra: usize) -> Expr {
    let mut arrow_params = Vec::with_capacity(arg.arrow_params.len());
    for ex in &arg.arrow_params {
        arrow_params.push(
            deepen(ex, arg_ctx_size, extra)
        );
    }
    let mut tail = Vec::with_capacity(arg.tail.len());
    for ex in &arg.tail {
        tail.push(
            deepen(ex, arg_ctx_size, extra)
        );
    }
    let mut head = arg.head;
    if let Ident::Local(i) = &mut head {
        if *i >= arg_ctx_size {
            *i += extra;
        }
    }
    Expr { arrow_params, head, tail }
}

