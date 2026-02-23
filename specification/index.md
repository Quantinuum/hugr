# HUGR Specification

The Hierarchical Unified Graph Representation (HUGR, pronounced *hugger*
🫂) is a proposed new
common internal representation used across TKET2, Tierkreis, and the L3
compiler. The HUGR project aims to give a faithful representation of
operations, that facilitates compilation and encodes complete programs,
with subprograms that may execute on different (quantum and classical)
targets.

![](/hugr/assets/hugr_logo.svg)

## Motivation

Multiple compilers and tools in the Quantinuum stack use some graph-like
program representation; be it the quantum circuits encoded as DAGs in
TKET, or the higher-order executable dataflow graphs in Tierkreis.

The goal of the HUGR representation is to provide a unified structure
that can be shared between the tools, allowing for more complex
operations such as TKET optimizations across control-flow blocks, and
nested quantum and classical programs in a single graph.
The HUGR should provide a generic graph representation of a program,
where each node contains a specific kind of operation and edges
represent (typed) data or control dependencies.

### Goals

- Modular design, allowing new operations, data types, and rewrite
  methods defined by third-parties.
- Represent mixed quantum-classical programs, allowing for efficient
  lowering through bespoke compilation to dedicated targets.
- Efficiently serializable. Different tools should be able to send and
  receive HUGRs via a serialized interface when sharing the in-memory
  structure is not possible.
- Provide a common interface for rewrite operations with support for
  opaque types.

### Non-goals

- Translations to other representations. While the HUGR should be able
  to encode programs in languages such as QIR, the translation should
  be implemented separately.
- Execution, or any kind of interpretation of the program. The HUGR
  describes the graph representation and control flow, without fixing
  the semantics of any extension operations defined outside the core
  set in this document, which will be most in actual use.

### Main requirements

- A directed graph structure with extensible operation types in the
  nodes and data types in the edges.
- Indexed connection ports for each operation node, which may be
  connected to another port with the same data type or remain
  unconnected.
- Control-flow support with ability to capture both LLVM SSACFG style
  programs and programs from future front-ends designed to target
  HUGR. These include the [guppylang](https://github.com/quantinuum/guppylang)
  Python eDSL for quantum-classical programming,
  and BRAT (which already uses an internal graph-like
  representation for classical functional programs and quantum
  kernels). We expect that these front-ends will provide
  programmer-facing control flow constructs that map to the preferred
  constructs in HUGR without first having to pass through an
  LLVM/SSACFG intermediate.
- Support for nested structures. The nodes form a tree-like hierarchy
  with nested graphs encoded as children of their containing node.
- User-defined metadata, such as debug information, can be efficiently
  attached to nodes and queried.
- All user-provided information can be encoded and decoded in a stable
  (versioned) efficient serialized format.
- A type system for checking valid operation connectivity + (nice to
  have) only operations supported on specific targets are used.
- A space efficient and user friendly specification of a subgraph and
  replacement graph, along with an efficient routine for performing
  the replacement.

## Contents

This specification is organized into the following sections:

- [Motivation](#motivation)
- [HUGR: Structure and Semantics](https://github.com/quantinuum/hugr/blob/main/specification/hugr.md)
- [Type System](https://github.com/quantinuum/hugr/blob/main/specification/type-system.md)
- [Replacement and Pattern Matching](https://github.com/quantinuum/hugr/blob/main/specification/rewriting.md)
- [Serialization](https://github.com/quantinuum/hugr/blob/main/specification/serialization.md)
- [Standard Library](https://github.com/quantinuum/hugr/blob/main/specification/stdlib.md)
- [Core Metadata Specification](https://github.com/quantinuum/hugr/blob/main/specification/metadata.md)
- [Architecture](https://github.com/quantinuum/hugr/blob/main/specification/appendices.md#architecture)
- [Glossary](https://github.com/quantinuum/hugr/blob/main/specification/appendices.md#glossary)
- Appendices
  - [Rationale for Control Flow](https://github.com/quantinuum/hugr/blob/main/specification/appendices.md#appendix-rationale-for-control-flow)
  - [Node types and their edges](https://github.com/quantinuum/hugr/blob/main/specification/appendices.md#appendix-node-types-and-their-edges)
  - [Binary `compute_signature`](https://github.com/quantinuum/hugr/blob/main/specification/appendices.md#appendix-binary-compute-signature)
