# Extension System

## Goals and constraints

The goal here is to allow the use of operations and types in the
representation that are user defined, or defined and used by extension
tooling. These operations cover various flavours:

- Instruction sets specific to a target.
- Operations that are best expressed in some other format that can be
  compiled into a graph (e.g. ZX).
- Ephemeral operations used by specific compiler passes.

A nice-to-have for this extensibility is a human-friendly format for
specifying such operations.

The key difficulty with this task is well stated in the [MLIR Operation
Definition Specification
docs](https://mlir.llvm.org/docs/DefiningDialects/Operations/#motivation)
:

> MLIR allows pluggable dialects, and dialects contain, among others, a
> list of operations. This open and extensible ecosystem leads to the
> "stringly" type IR problem, e.g., repetitive string comparisons
> during optimization and analysis passes, unintuitive accessor methods
> (e.g., generic/error prone `getOperand(3)` vs
> self-documenting `getStride()`) with more generic return types,
> verbose and generic constructors without default arguments, verbose
> textual IR dumps, and so on. Furthermore, operation verification is:
>
> 1\. best case: a central string-to-verification-function map
>
> 2\. middle case: duplication of verification across the code base, or
>
> 3\. worst case: no verification functions.
>
> The fix is to support defining ops in a table-driven manner. Then for
> each dialect, we can have a central place that contains everything you
> need to know about each op, including its constraints, custom assembly
> form, etc. This description is also used to generate helper functions
> and classes to allow building, verification, parsing, printing,
> analysis, and many more.

As we see above MLIR's solution to this is to provide a declarative
syntax which is then used to generate C++ at MLIR compile time. This is
in fact one of the core factors that ties the use of MLIR to C++ so
tightly, as managing a new dialect necessarily involves generating,
compiling, and linking C++ code.

We can do something similar in Rust, and we wouldn't even need to parse
another format, sufficiently nice rust macros/proc\_macros should
provide a human-friendly-enough definition experience.  These extensions can be
serialized as JSON for use in other tools.

Ultimately though, we cannot avoid the "stringly" type problem if we
want *runtime* extensibility - extensions that can be specified and used
at runtime. In many cases this is desirable.

(extension-implementation)=
## Extension Implementation

Extensions may provide a number of named **TypeDef**s and **OpDef**s.
These are (potentially polymorphic) definitions of types and operations, respectively---polymorphism arises because both may
declare any number of TypeParams, as per [Polymorphism](#polymorphism). To use a TypeDef as a type,
it must be instantiated with TypeArgs appropriate for its TypeParams, and similarly
to use an OpDef as a node operation: each `ExtensionOp` node stores a static-constant list of TypeArgs.

For TypeDef's, any set of TypeArgs conforming to its TypeParams, produces a valid type.
However, for OpDef's, greater flexibility is allowed: each OpDef *either*

1. Provides a polymorphic type scheme, as per [Type System](#type-system), which may declare TypeParams;
   values (TypeArgs) provided for those params will be substituted in. *Or*
2. The extension may self-register binary code (e.g. a Rust trait) providing a function
   `compute_signature` that fallibly computes a (perhaps-polymorphic) type scheme given some initial type arguments.
   The operation declares the arguments required by the `compute_signature` function as a list
   of TypeParams; if this successfully returns a type scheme, that may have additional TypeParams
   for which TypeArgs must also be provided.

For example, the TypeDef for `array` in the prelude declares two TypeParams: a `BoundedUSize`
(the array length) and a `Type`. Any valid instantiation (e.g. `array<5, usize>`) is a type.
Much the same applies for OpDef's that provide a `Function` type, but binary `compute_signature`
introduces the possibility of failure (see full details in [appendix](appendix-compute-signature.md)).

When serializing the node, we also serialize the type arguments; we can also serialize
the resulting (computed) type with the operation, and this will be useful when the type
is computed by binary code, to allow the operation to be treated opaquely by tools that
do not have the binary code available. (That is: the serialized JSON, including all types
but only OpDefs that do not have binary `compute_signature`, can be sent with the HUGR).

This mechanism allows new operations to be passed through tools that do not understand
what the operations *do*---that is, new operations may be be defined independently of
any tool, but without providing any way for the tooling to treat them as anything other
than a black box. Similarly, tools may understand that operations may consume/produce
values of new types---whose *existence* is carried in the JSON---but the *semantics*
of each operation and/or type are necessarily specific to both operation *and* tool
(e.g. compiler or runtime).

However we also provide ways for extensions to provide semantics portable across tools.
For types, there is a fallback to serialized json; for operations, extensions *may* provide
either or both:

1. binary code (e.g. a Rust trait) implementing a function `try_lower`
   that takes the type arguments and a set of target extensions and may fallibly return
   a subgraph or function-body-HUGR using only those target extensions.
2. a HUGR, that declares functions implementing those operations. This
   is a simple case of the above (where the binary code is a constant function) but
   easy to pass between tools. However note this will only be possible for operations
   with sufficiently simple type (schemes), and is considered a "fallback" for use
   when a higher-performance (e.g. native HW) implementation is not available.
   Such a HUGR may itself require other extensions.

Whether a particular OpDef provides binary code for `try_lower` is independent
of whether it provides a binary `compute_signature`, but it will not generally
be possible to provide a HUGR for an operation whose type cannot be expressed
using a polymorphic type scheme.
