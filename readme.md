
Lofer
=====

Lofer is a dependently typed functional language that combines the simplicity
of Scheme with the expressiveness of Agda/Coq.

The project was originally intended to be part of a grander dependently typed
_procedural_ programming language, however such a language would be so
complicated that it ought to be explored from the bottom up, probably starting
with agda-internalized models first.

I have since remade it around the concept of postulates with computation rules,
making the implementation simultaneously simpler and more general: the only
builtin types are now pi types and universes!

The language also uses strict evaluation, which has already had an impact on my
understanding of functional programming, but this may change depending on how
difficult it is to use church encodings with strict evaluation.

Like most experimental dependently typed languages, this language has none of
the quality of life feature that make Agda or Coq usable and sound:
- no inference/implicit parameters
- no instance variables
- no case/auto tactics
- no pattern matching
- no recursion (you need to introduce a fixpoint postulate using the usual
  definition)
- no inductive data types!
- no universe levels/universe consistency checks
- no termination checks, (in the case that you do introduce a fixpoint)
- no lambda unification... functions with different names are never equal
  without assuming extensionality
- no lambdas or with/where semantics! this may change once I learn what I want
  to learn about strict evaluation.

beyond this the current implementation also has abysmal error messages, with
no reference to line numbers/columns, and fully evaluated, anonymized
identifiers.

`f A B x y = y x` might complain with something like
"x2 has type x0 but was expected to have type x0 -> x1 x4"

this means that if you are interested in real proof assistance or dependently
typed programming, agda should be preferred, (or whatever interactive proof
assistant suits your fancy) however, this language is particularly well suited
to foundational experiments for figuring out new alternatives to the features
listed above.

In short the purpose of this language is to allow one to add exotic postulates,
such as type-level representations of 'constructive recursion', and attempt to
prove their inconsistency as rapidly as possible.

At some point I may add quality of life features such as inductive data types
or pattern matching, but I would be particularly interested in implementing
these as syntax sugars rather than explicit language objects.

I may also add features related to writing full type eliminators for pure
calculus of constructions, should I find something that can't be represented as
a type-level postulate.

Program
=======

The program currently parses a single file, type checking each line in the
context of the previous lines.
It does not execute any functions unless they appear in the type declarations
of other functions.

To use the program, run `cargo run -- "file"`

It will then print the types of each function that successfully type checks,
along with a single error/success message.

If there is an error in one function the program will stop altogether, though
with better error handling it might be able to continue in the future.

Language
========

Syntax
------

A program is a series of function annotations + definitions,
which take the form:
```
function_name: expression
function_name arg_name1 arg_name2 = expression
```

comments are begun with "--", and multiple lines are concatenated by ending one
line with `\`.
These can be combined with `\--` though the middle of a line probably isn't the
best place for a comment.

for now all identifiers (function names and argument names) start with a letter
or with `_`, followed by any number of letters, numbers, and `_`s, and finished
with some number of apostrophes.

An expression is basically either a variable applied to a sequence of
subexpressions, as is typical of functional programming, or a sequence of
annotations separated by arrows, when representing pi/exponential types. e.g.
```
flip: (A: Type) -> (B: Type) -> (C: Type) -> (A -> B -> C) -> B -> A -> C
flip A B C f y x = f x y
```

While it is typical for annotations to be arrow expressions and definitions to
be function applications, the two can be freely mixed.

```
Exp: Type -> Type -> Type
Exp A B = A -> B

Thing: flip Type Type Type Exp ((B: Type) -> B -> Type) Type
Thing A B x = (C: B -> Type) -> C x -> (y: B) -> C y
```

Finally annotations that start with the word `postulate` can have any
definition (won't be type checked at all) or no definition.

It is recommended to give definitions to any postulates that aren't types, and
to test postulates in simple equality lemmas to make sure that they still
handle their parameters correctly.

Type Checking
-------------

Type checking is straight forward.
Given an annotation and a definition, the type checker determines both of their
types, and compares them. An error can occur in any of the following
conditions:
- the annotation has no type (a function was applied to the wrong type)
- the annotation isn't of type `Type`
- the annotation cannot be evaluated (a type was somehow applied to arguments)
additionally if the term is not declared to be a postulate, the following
conditions also trigger an error:
- the definition has too many parameters for the given annotation
- the definition has no type
- the definition's type cannot be evaluated
- the definition's type does not match the annotation

Evaluation only occurs in the above contexts, there is no way to evaluate a
function other than by type checking another function.

The type system is just that of any martin-lof type theory.

Functions can have dependent types, `f : (x: A) -> B(x)`

Function evaluation also evaluates types: `(f y) : B(y)` assuming that y has
type `A`

Arrow expressions immediately have the type `Type`, but won't type check unless
each parameter along with the final output check as having the type `Type`

`Type` has the type `Type`, which is apparently inconsistent.

Finally postulates are assumed to have the type given, which can generate
absurd expressions that may eventually cause a runtime error.

```
f: (A: Type) -> A -> Type
f x = x Type
```

See proto.ls for an example of how church encoding can be hidden behind
postulates to create algebraic data types with standard eliminators and
computation rules.

Evaluation Semantics
--------------------

Unlike typical dependently typed languages, the current implementation of lofer
is strict call-by-value, and uses partially applied functions to avoid lambdas
altogether. (Although lambda like semantics still exist in the type families in
arrow expressions, since a lot more than just equational reasoning is lost if
pi types can't evaluate.)
It would be possible to add lambdas and lambda unification in the future, but
for now since strict evaluation changes so much I personally prefer explicit
function definitions anyway.

Functions do not evaluate until they get the specific number of parameters
listed in their original definition, at which point they _immediately
evaluate_, regardless of whether the enclosing function application needs to
evaluate.
Evaluation is done as one would expect, by substituting the arguments into the
definition of the function to get a resul.

One consequence of this is that all functions are essentially a family of data
structures containing very specific data types, which is very unusual for a
referentially transparent language.

If you want lazy semantics you must make them explicit, typically by
postulating a `Unit` type, and a `tt` term to populate it, and then adding a
trivial `Unit` input to the end of any function that must be evaluated lazily.

it is important to note that `const A Unit (x y z)` will not suffice to
postpone the calculation of x y z. One must
construct an explicit function `f x y z _ = x y z` and then partially apply
that.

This means many simple functional algorithms must make their laziness explicit,
e.g.
```
foldr: (A: Type) -> (B: Type) -> (A -> (Unit -> B) -> B) -> B -> \
  List A -> Unit -> B
foldr A B f acc (Cons x xs) tt = f x (foldr A B f acc xs)
```
noting that the above relies on recursion and pattern matching not available in
Lofer.

Particularly the fixpoint combinator would have the following type:
```
postulate fix: (A: Type) -> ((Unit -> A) -> A) -> Unit -> A
-- fix A f tt = f (fix A f)
```

This allows for short circuiting either for proper termination or better
performance as normal.

On the other hand strict semantics are the default and no `seq` operator is
needed. e.g.
```
foldl A B f acc (Cons x xs) = foldl A B f (f acc x) xs
```
would immediately perform as desired without constructing a thunk chain, unless
`f acc x` really does construct a thunk chain by partially applying some
function somehow.

This choice was made in the spirit of referential transparency, but is
generally an interesting space to explore compared to the standard lazy
semantics of most functional programming.

