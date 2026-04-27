# HUGR Guide

This is an informal, conceptual guide to HUGR aimed at those who wish to work
directly with this structure and understand the motivations behind it.

We usually describe HUGR as an [intermediate representation](https://en.wikipedia.org/wiki/Intermediate_representation)
(IR), designed specifically for the representation of programs that work with
quantum (as well as classical) data.

This is only somewhat accurate. The most common workflow is for the programmer to write
in a higher-level language (such as guppy), which is then compiled to HUGR, which
is further processed (optimized, further lowered, and submitted to devices and
simulators). In this workflow, the programmer need have no knowledge of HUGR
internals, simply passing it around as a black box (e.g. an opaque Python object or
a file).

However, there are cases where we may wish to construct and manipulate HUGR
directly. This is necessary when writing custom compilation passes or extensions,
or when more
fine-grained control over the executed code is required than is possible from
guppy, for example.

In addition, what we mean by "HUGR" is a little ambiguous. The formal [specification](../specification/index.md)
defines it as a mathematical structure. Code in this repo defines an in-memory Rust representation,
an in-memory Python representation, and a serialized representation. It is this
last that is closest to a true "IR", and is most useful as an interchange format, but it is not practically manipulable except by going through one of the in-memory forms.

## Why HUGR?

The circuit model of quantum circuits proves insufficient when classical control flow is
introduced, since it cannot capture loops or conditional blocks, so a more general
representation of quantum programs is required. Nevertheless, the circuit model
is extremely useful for optimization of purely quantum subprograms. HUGR was
designed as a generalization of the circuit model to more general programs with
control flow. It adopts a _hierarchical_ structure, where nodes in the graph (operations)
may either be atomic or contain subgraphs. For example, a loop is represented by
a special kind of node (`TailLoop`) which contains within it the full graph of
operations inside the loop, with an additional output that determines whether to
continue or repeat the loop.

Another design principle is that of easy extensibility: rather than defining a
full set of operations in terms of which all programs have to be expressed, HUGRs
may use operations (and types) drawn from arbitrary _extensions_. Indeed, HUGR
itself defines almost no operations; instead it defines a scaffold onto which
operations defined in extensions can be attached. A given extension can of course
be shared across many different HUGRs.

## The basic node types

The HUGR [specification](../specification/index.md) contains a full description of
all the node types of a HUGR and their constraints. Here we give a brief overview.

### `Module` nodes

At the top level of the hierarchy is a root (module) node. The children of this
node are _functions_: either function definitions (`FuncDefn`) or function
declarations (`FuncDecl`).

### `FuncDefn` and `FuncDecl` nodes

A function definition (`FuncDefn`) node has a name, a signature (sequence of input and output types),
and a single child node which implements it. The child node may be one of several
types which we classify as _dataflow sibling graph_ (DSG) nodes. A DSG node just
represents an operation with fixed input and output tyoes. They may be atomic
operations, `DFG`, `CFG`, `TailLoop` or `Conditional` nodes (described below).

A function declaration (`FuncDecl`) node is just like a `FuncDefn` but without
the child node. The body of the function should be defined in a `FuncDefn`
elsewhere, possibly in a different HUGR.

Both `FuncDefn` and `FuncDecl` nodes may be "called" from `Call` nodes in the
HUGR.

### `DFG` nodes

The children of a `dataflow graph` (DFG) node form a directed acyclic graph.
They comprise an `Input` node, an `Output` node, and any number of intermediate
DSG nodes. As in a quantum circuit, data flows in one direction through the DFG,
being transformed by the nodes it passes through.

### `CFG` nodes

The children of a `control-flow graph` (CFG) node form a directed graph composed
of `BasicBlock` nodes. Two of these `BasicBlock` nodes are distinguished as the
entry and exit nodes. Each `BasicBlock` node except for the exit node is parent to
a DSG; it may have any number of successors, one of which is chosen at runtime
by means of a special output.

### `TailLoop`, `Conditional` and `Case` nodes

The `CFG` nodes defined above represent fully general control-flow graphs. In practice,
most control flow is structured as loops and conditionals. Defining dedicated
node types for these not only simplifies the representation of these common patterns
but also assists with compilation.

A `TailLoop` node is parent of a DSG implementing the inner logic, with an additional
boolean output to decide whether to continue or repeat the loop.

A `Conditional` node is parent to a number of `Case` nodes, which are themselves
parents of DSGs. Which of these `Case` nodes is executed depends on a special
input value.

### `LoadConstant`, `Const`, `Call` and `LoadFunction`.

These node types all convert static data (constants or function definitions)
into dynamic (runtime) data.

A `LoadConstant` node just loads a static constant into memory from a `Const` node, which
defines the value of the constant.

A `LoadFunction` node loads a static function into memory from a `FuncDefn` or
`FuncDecl` node, specifying any parameters needed if the function is polymorphic.
Once loaded, the function is treated as a (higher-order) value.

A `Call` node calls a `FuncDefn` or `FuncDecl` node directly, generating the
output of the function.

## Custom operations and types

Most "atomic" operations and types are defined in extensions (see below). For
example, integer types of various bit widths (from 1-bit to 64-bit), and
operations on them, are defined in the `arithmetic.int.types` and
`arithmetic.int.ops` extensions. Core HUGR only provides primitives for
constructing sums and tuples of type; however there is a standard library of
commonly used operations and types (integers, floats, arrays and so on). The
qubit type and quantum operations are provided in an extension from TKET.

## Entrypoints

A HUGR may have one node distinguished as its "entrypoint". For executable HUGRs
this marks the node where execution begins.

## HUGR packages

A HUGR package consists of a collection of HUGRs, together with a collection of
extensions that the HUGRs in the package may depend on.

## Building, saving and loading HUGR packages

The [HUGR repository](https://github.com/Quantinuum/hugr) contains two independent
implementations of the HUGR structure, one in Rust and one in Python. The Rust
implementation is published as [crate](https://crates.io/crates/hugr) on `crates.io`
(documentation [here](https://docs.rs/hugr/latest/hugr/index.html)),
while the Python implementation is published as a [package](https://pypi.org/project/hugr/) on `pypi` (documentation [here](https://quantinuum.github.io/hugr/generated/hugr.html)).

Both implementations provide functions to convert to and from the serialized
"envelope" format, so HUGRs can be shared between them and also shered with
other libraries such as TKET.

### Rust

[HUGR Rust tutorial](./tutorial-rust.md)

### Python

[HUGR Python tutorial](./tutorial-python.md)

## Visualization tools

## HUGR Extensions

### Introduction

### Defining an extension

## Importing HUGR from other formats

## Compilation

### Basic compilation passes

### Using TKET1 passes

### Defining custom passes

## Lowering
