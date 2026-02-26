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

The majority of types will be Opaque ones defined by extensions including the [standard library](stdlib.md#standard-library). However a number of types can be constructed using only the core type constructors: for example the empty tuple type, aka `unit`, with exactly one instance (so 0 bits of data); the empty sum, with no instances; the empty Function type (taking no arguments and producing no results - `void -> void`); and compositions thereof.

Sums are `CopyableType` if all their components are; they are also fixed-size if their components are.

(polymorphism)=
## Polymorphism

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

The same mechanism is also used for polymorphic OpDefs, see [Extension Implementation](extensions.md#extension-implementation).

(extension-tracking)=
## Extension Tracking

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
as arguments to Opaque types---see [Extension System](extensions.md).)

### Row Variables

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
