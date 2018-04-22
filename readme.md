
Lofer
=====

Lofer is a dependently typed functional language that combines the simplicity
of Scheme with the strength of Agda/Coq.

The intention is to use this as a substrate for other more useful languages,
such that a procedure in one language is a normal object in Lofer.

For now though it is an interesting toy for those interested in type theory
and/or functional programming.

Program
=======

The program currently parses human readable code, executes it,
(without type checking) and displays the result as a lambda expression.

To use the program, run `cargo run -- "file1" "file2" ...`
Each file will be parsed into a single expression, and then the first
expression will be applied to the second, then this to the third, and so on.

The resulting expression is then evaluated, and printed to the screen.

Note
----

Functions are not internally evaluated, so you will need to apply them to
arguments to get sane/readable results.

Note that there is no type checker, which does defeat the purpose of having
a dependently typed language.
The type checker was implemented a while ago, but after refactoring it was
never fully reimplemented.

The plan is to implement the type checker within lofer itself.


Also the errors aren't very helpful at all!


Language
========

Syntax
------

A program is a series of function definitions, which take the form:
```
function_name (arg_name: ArgType) (arg_name: ArgType) = expression
```

one can replace `ArgType` with `_` since the type checker currently doesn't
work.

Most expressions are just haskell-style function applications, e.g.
```
flip (f: Pi x: A, Pi y: B, C) (y: B) (x: A) = f x y
```

Further, lines can be indented to have access to the args of a previous
function:
```
flip (f: _) = f_flipped
  f_flipped (y: B) (x: A) = f x y
```

The last unindented line of a program is the program's output.

The language cannot directly recurse, and to enforce this, you cannot refer
to functions before they have been defined.
Instead see `fix` for a very rough explanation on how to recurse.

Semantics
---------

Conceptually the language has 6 types/connectives,
- Void (has no values)
- Unit (has one value: `tt`)
- Bool (has two values: `true` and `false`)
- Sigma (combines a type with a type family, basically pair type)
- Pi (maps one type to a type family, basically function type)
- Type, the type of all types

Sigma and Pi are dependently typed, which lets you write types like
```
Pi x: Bool, bool_elim _ Unit Bool x
```
which is the type of functions that map `true` to `tt` and `false` to some
Bool.


The builtin terms for handling these types are:
- `tt`, `true`, `false` values
- `pair` function which turns two values into a pair
- `void_elim` and `unit_elim` which serve no computational role, but have
  useful types when making safe programs.
- `bool_elim` and `sigma_elim` which make data types usable

additionally the `fix` term is used to achieve recursion.

The data terms have the following types:
```
tt: Unit
true: Bool
false: Bool
pair: Pi Fst: Type, Pi Snd: (Pi _: Fst, Type),
  Pi x0: Fst, Pi y: Snd x0, Sigma x1: Fst, Snd x1
```

And the eliminators have the following types (For the brave)
```
void_elim: Pi A: Type, Pi _: Void, A
unit_elim: Pi A: (Pi _: Unit, Type),
  Pi _: A tt, Pi x: Unit, A x
bool_elim: Pi A: (Pi _: Bool, Type),
  Pi t: A true, Pi f: A false, Pi x: Bool, A x
sigma_elim: Pi Fst: Type, Pi Snd: (Pi _: Fst, Type),
  Pi Out: (Pi _: (Sigma x: Fst, Snd x), Type),
    Pi f: (Pi x: Fst, Pi y: Snd x, Out (pair x y)),
      Pi p: (Sigma x: A, B x), Out p
```

These last two eliminators are better understood by what they actually do:

`bool_elim` is an if-then-else function, that takes two branches, and returns
one of them based on the bool input. (It takes the branches before it takes the
bool though!)

`sigma_elim` is uncurry, it takes a function like `a -> b -> c` and turns it
into a function like `(a, b) -> c`

The `fix` function is a fixpoint combinator, it takes a generating function,
and applies it to itself infinitely.

`fix` has the following type:
`fix: Pi A: Type, Pi f: (Pi _: A, A), A`

Be warned, `fix` can result in very unreadable functions if not fully
evaluated.

Fix can be used to make recursive types and recursive functions.

In haskell one would write `f x y = something f x y`
but with fix one must instead write
```
f = fix f_gen
  f_gen f_prev = f_next
    f_next x y = something f_prev x y
```

