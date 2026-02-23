# Type System

There are two classes of type: `AnyType` $\supset$ `CopyableType`. Types in these
classes are distinguished by whether the runtime values of those types can be implicitly
copied or discarded (multiple or 0 links from on output port respectively):

- For the broadest class (`AnyType`), the only operation supported is the identity operation (aka no-op, or `lift` - see [Extension Tracking](#extension-tracking) below). Specifically, we do not require it to be possible to copy or discard all values, hence the requirement that outports of linear type must have exactly one edge. (That is, a type not known to be in the copyable subset).

    In fully qubit-counted contexts programs take in a number of qubits as input and return the same number, with no discarding.

- The smaller class is `CopyableType`, i.e. types holding ordinary classical
  data, where values can be copied (and discarded, the 0-ary copy). This
  allows multiple (or 0) outgoing edges from an outport; also these types can
  be sent down `Const` edges.

Note that all dataflow inputs (`Value`, `Const` and `Function`) always require a single connection, regardless of whether the type is `Linear` or `Copyable`.

**Rows** The `#` is a *row* which is a sequence of zero or more types. Types in the row can optionally be given names in metadata i.e. this does not affect behaviour of the HUGR. When writing literal types, we use `#` to distinguish between tuples and rows, e.g. `(int<1>,int<2>)` is a tuple while `Sum(#(int<1>),#(int<2>))` contains two rows.

The Hugr defines a number of type constructors, that can be instantiated into types by providing some collection of types as arguments. The constructors are given in the following grammar:

```haskell

Extensions ::= (Extension)* -- a set, not a list

Type ::= Sum([#]) -- disjoint union of rows of other types, tagged by unsigned int
       | Opaque(Name, [TypeArg]) -- a (instantiation of a) custom type defined by an extension
       | Function(#, #, Extensions) -- monomorphic function: arguments, results, and delta (see below)
       | Variable -- refers to a TypeParam bound by the nearest enclosing FuncDefn node or polymorphic type scheme
```

(We write `[Foo]` to indicate a list of Foo's.)

Tuples are represented as Sum types with a single variant. The type `(int<1>,int<2>)` is represented as `Sum([#(int<1>,int<2>)])`.

The majority of types will be Opaque ones defined by extensions including the [standard library](#standard-library). However a number of types can be constructed using only the core type constructors: for example the empty tuple type, aka `unit`, with exactly one instance (so 0 bits of data); the empty sum, with no instances; the empty Function type (taking no arguments and producing no results - `void -> void`); and compositions thereof.

Sums are `CopyableType` if all their components are; they are also fixed-size if their components are.

### Polymorphism

While function *values* passed around the graph at runtime have types that are monomorphic,
`FuncDecl` and `FuncDefn` nodes have not types but *type schemes* that are *polymorphic*---that is,
such declarations may include (bind) any number of type parameters, of kinds as follows:

```haskell
TypeParam ::= Type(Any|Copyable)
            | BoundedUSize(u64|) -- note optional bound
            | Extensions
            | String
            | Bytes
            | Float
            | List(TypeParam) -- homogeneous, any sized
            | Tuple([TypeParam]) -- heterogenous, fixed size
            | Opaque(Name, [TypeArg]) -- e.g. Opaque("Array", [5, Opaque("usize", [])])
```

The same mechanism is also used for polymorphic OpDefs, see [Extension Implementation](#extension-implementation).

Within the type of the Function node, and within the body (Hugr) of a `FuncDefn`,
types may contain "type variables" referring to those TypeParams.
The type variable is typically a type, but not necessarily, depending upon the TypeParam.

When a `FuncDefn` or `FuncDecl` is `Call`ed, the `Call` node statically provides
TypeArgs appropriate for the function's TypeParams:

```haskell
TypeArg ::= Type(Type) -- could be a variable of kind Type, or contain variable(s)
          | BoundedUSize(u64)
          | String(String)
          | Bytes([u8])
          | Float(f64)
          | Extensions(Extensions) -- may contain TypeArg's of kind Extensions
          | List([TypeArg])
          | Tuple([TypeArg])
          | Opaque(Value)
          | Variable -- refers to an enclosing TypeParam (binder) of any kind above
```

For example, a Function node declaring a `TypeParam::Opaque("Array", [5, TypeArg::Type(Type::Opaque("usize"))])`
means that any `Call` to it must statically provide a *value* that is an array of 5 `usize`s;
or a Function node declaring a `TypeParam::BoundedUSize(5)` and a `TypeParam::Type(Linear)` requires two TypeArgs,
firstly a non-negative integer less than 5, secondly a type (which might be from an extension, e.g. `usize`).

Given TypeArgs, the body of the Function node's type can be converted to a monomorphic signature by substitution,
i.e. replacing each type variable in the body with the corresponding TypeArg. This is guaranteed to produce
a valid type as long as the TypeArgs match the declared TypeParams, which can be checked in advance.

(Note that within a polymorphic type scheme, type variables of kind `List`, `Tuple` or `Opaque` will only be usable
as arguments to Opaque types---see [Extension System](#extension-system).)

#### Row Variables

Type variables of kind `TypeParam::List(TypeParam::Type(_))` are known as
"row variables" and along with type parameters of the same kinds are given special
treatment, as follows:
* A `TypeParam` of such kind may be instantiated with not just a `TypeArg::List`
  but also a single `TypeArg::Type`. (This is purely a notational convenience.)
  For example, `Type::Function(usize, unit, <exts>)` is equivalent shorthand
  for `Type::Function(#(usize), #(unit), <exts>)`.
* When a `TypeArg::List` is provided as argument for such a TypeParam, we allow
  elements to be a mixture of both types (including variables of kind
  `TypeParam::Type(_)`) and also row variables. When such variables are instantiated
  (with other `List`s) the elements of the inner `List` are spliced directly into
  the outer (concatenating their elements), eliding the inner (`List`) wrapper.

For example, a polymorphic FuncDefn might declare a row variable X of kind
`TypeParam::List(TypeParam::Type(Copyable))` and have as output a (tuple) type
`Sum([#(X, usize)])`. A call that instantiates said type-parameter with
`TypeArg::List([usize, unit])` would then have output `Sum([#(usize, unit, usize)])`.

Note that since a row variable does not have kind Type, it cannot be used as the type of an edge.

## Extension System

### Goals and constraints

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

### Extension Implementation

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
introduces the possibility of failure (see full details in [appendix](#appendix-3-binary-compute_signature)).

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
