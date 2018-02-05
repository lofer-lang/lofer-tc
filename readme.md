
Dependent Type Theory
=====================

Having spent a lot of time thinking about languages I like, and features I
don't like, and eventually discovering DTT, I have finally come up with a
formulation for a programming language that I feel does everything I want.

In summary there are two languages, a dependently typed functional language,
and an internalized imperative language. (inspired by IO in haskell etc.)
The imperative language however, is a true imperative language; actions are not
a monad, they are a category whose objects are machine states.

The functional code will be designed to serialize into a portable form,
whereas the imperative code will be designed to translate into LLVM,
implemented by simply pattern matching on possible programs and recursing.

There are two core ideas that this setup has in mind:

Being dependently typed, the functional language could be used to represent
safety guarantees, which could be baked into your imperative programs.

Additionally, by having universes, the functional language could represent
 - module systems,
 - polymorphism,
 - encapsulation,
 - dependency inversion,
all in the same way, as dependent tuples like `(type, methods)` and/or
dependent functions `\(type, method) -> method`.

Structure
=========

Being a very expressive, low level programming language, it seems it would be
a good idea to head towards a self-hosting representation.
What follows is an outline of how this could be done.

Evaluator
---------

The evaluator is meant to be a program that takes a dependently typed
expression, and fully computes any possible beta reductions, outputting the
result.

The actual implementation would need to be a pipeline that loads/deserialized a
functional program from files, evaluates it, then serializes the output to a
file.

Linking multiple files could actually be done as a beta reduction, applying
your linker program to all of your 'modules'.
For this reason the evaluator would likely take a series of filenames as input,
load each file, and repeatedly apply the first file's contents to the others'.

Boot Evaluator
--------------

The above evaluator could be written in the imperative language, and then
evaluate itself into LLVM code, but that requires a bootstrap implementation.

The boot evaluator fills this role, fairly straight-forward.

Boot Parser
-----------

Writing programs in serialized binary format would be very painful in the long-
term, which is why, like most languages, programs will be written in a human-
readable form, and then programmatically translated into the serialized form.

Parsing is an exceptionally good application of functional programming, and so
writing a self hosting parser would be very useful, but until then, a boot
parser would need to translate the base syntax into bytes.

Base Parser
-----------

The base parser would be the functional implementation of the parser, seeking
only to replicate the boot parser, while adding a macro system.

This means the base parser would define a parsing tree, and then populate it
sufficiently to parse itself.

Standard Parser
---------------

This is not so much a separate parser, as it is an initial parse tree designed
to be more sane than the base parser.

The base syntax is designed as a 1-to-1 representation of the serialized form,
but even this syntax is painful as structures grow in complexity, when you have
to write such foundational definitions of everything.

The standard parser can be implemented by simply writing a number of macro
definitions, and applying the base parser to them.

Missing Link(er)
----------------

The above system currently does not consider layout of files in a file-system.
Languages such as Rust use the file-system to represent and in fact specify
the module layout of programs, and doing anything like that requires an initial
detail that the parsers be passed a full directory tree, rather than individual
files.

Type System
===========

The type system is meant to be very small.

Void Type
---------

This type has no constructors, it represents the empty set, unprovable
theorems, etc.

Unit Type
---------

This type has a single constructor, and can be used to fill gaps in definitions
of complex types, e.g. as the contents of the Zero constructor in Peano
arithmetic.

Bool Type
---------

This type has two constructors, and is necessary to define any compound data
types at all.

Sigma Type
----------

The classic dependent pair.
By writing a family of types for the second term, dependent pairs can be
constructed with the property that `p2 pair` has type `family(p1 pair)` where
`family` is the family of types, and `pair` is the dependent pair.

Pi Type
-------

Like Sigma types, but a function, so that `func(arg)` has type `family(arg)`.

Universe Types
--------------

Getting things done with these types immediately requires a notion of universe.
The idea is that there are a series of universes, starting with `U_1`, where
 - `U_1` is the type of all types that can be constructed out of the above
   connectives,
 - `U_2` is like `U_1`, with the addition of `U_1` as a primitive type.
   This means types can be expressions now, e.g. `if x then Unit else Void`
 - `U_3` has both `U_1` and `U_2` as primitives, and so on.

When working with universes there tends to be redundancy, writing functions
that are identical, except for the input parameter being the next universe up.
This leads to the idea of poly-universality, where expressions are interpreted
as algebraic `Type_n -> something` where `n` can be chosen at any time, and the
resulting expression exists within `Type_n+1`.

Whether expressions are actually treated as poly-universal, or there is simply
a `promote` primitive that bumps an expression up one, is an implementation
detail.

