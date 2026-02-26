# HUGR Specification

The Hierarchical Unified Graph Representation (HUGR, pronounced *hugger*
🫂) is a proposed new
common internal representation used across TKET2, Tierkreis, and the L3
compiler. The HUGR project aims to give a faithful representation of
operations, that facilitates compilation and encodes complete programs,
with subprograms that may execute on different (quantum and classical)
targets.

![](/hugr/assets/hugr_logo.svg)

## Contents

This specification is organized into the following sections:

- [Motivation](motivation.md)
- [HUGR: Structure and Semantics](hugr.md)
- [Type System](type-system.md)
- [Replacement and Pattern Matching](rewriting.md)
- [Serialization](serialization.md)
- [Standard Library](stdlib.md)
- [Core Metadata Specification](metadata.md)
- [Architecture](architecture.md)
- [Glossary](glossary.md)
- Appendices
  - [Rationale for Control Flow](appendix-control-flow.md)
  - [Node types and their edges](appendix-node-types.md)
  - [Binary `compute_signature`](appendix-compute-signature.md)
