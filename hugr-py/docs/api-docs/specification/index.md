# HUGR Specification

The Hierarchical Unified Graph Representation (HUGR, pronounced *hugger*
🫂) is a proposed new
common internal representation used across TKET2, Tierkreis, and the L3
compiler. The HUGR project aims to give a faithful representation of
operations, that facilitates compilation and encodes complete programs,
with subprograms that may execute on different (quantum and classical)
targets.

```{include} ../../../../specification/motivation.md
```

```{toctree}
:maxdepth: 2
:caption: Specification

hugr
type-system
extensions
rewriting
serialization
stdlib
metadata
architecture
glossary
appendix-control-flow
appendix-node-types
appendix-compute-signature
```
