# Appendix: Rationale for Control Flow

## Justification of the need for CFG-nodes

- Conditional + TailLoop are not able to express arbitrary control
  flow without introduction of extra variables (dynamic overhead, i.e.
  runtime cost) and/or code duplication (static overhead, i.e. code
  size).
  - Specifically, the most common case is *shortcircuit evaluation*:
    `if (P && Q) then A; else B;` where Q is only evaluated if P is
    true.
- We *could* parse a CFG into a DSG with only Conditional-nodes and
  TailLoop-nodes by introducing extra variables, as per [Google
  paper](https://doi.org/10.1145/2693261), and then expect
  LLVM to remove those extra variables later. However that's a
  significant amount of analysis and transformation, which is
  undesirable for using the HUGR as a common interchange format (e.g.
  QIR → HUGR → LLVM) when little optimization is being done (perhaps
  no cross-basic-block optimization).
- It's possible that maintaining support for CFGs-nodes may become a
  burden, i.e. if we find we are not using CFGs much. However, I
  believe that this burden can be kept acceptably low if we are
  willing to drop support for rewriting across basic block boundaries,
  which would be fine if we find we are not using CFGs much (e.g.
  either we rely on turning relevant CFG/fragments into
  Conditional/TailLoop-nodes first, which might constitute rewriting
  in itself; or programmers are mainly using (our) front-end tools
  that build Conditional/TailLoop-nodes directly.)

…and the converse: we want `Conditional` and `TailLoop` *as well* as
`CFG` because we believe they are much easier to work with conceptually
e.g. for authors of "rewrite rules" and other optimisations.

## Alternative representations considered but rejected

- A [Google paper](https://doi.org/10.1145/2693261) allows
  for the introduction of extra variables into the DSG that can be
  eliminated at compile-time (ensuring no runtime cost), but only if
  stringent well-formedness conditions are maintained on the DSG, and
  there are issues with variable liveness.
- [Lawrence's
  thesis](https://doi.org/10.48456/tr-705)
  handles some cases (e.g. shortcircuit evaluation) but cannot handle
  arbitrary (even reducible) control flow and the multi-stage approach
  makes it hard to see what amount of code duplication will be
  necessary to turn the IR back into a CFG (e.g. following a rewrite).
- We could extend Conditional/TailLoop nodes to be more expressive
  (i.e. allowing them or others to capture *more* common cases, indeed
  arbitrary reducible code, in a DSG-like fashion), perhaps something
  like WASM. However although this would allow removing the CFG, the
  DSG nodes get more complicated, and start to behave in very
  non-DSG-like ways.
- We could use function calls to avoid code duplication (essentially
  the return address is the extra boolean variable, likely to be very
  cheap). However, I think this means pattern-matching will want to
  span across function-call boundaries; and it rules out using
  non-local edges for called functions. **TODO** are those objections
  sufficient to rule this out?

### Comparison with MLIR

There are a lot of broad similarities here, with MLIR's regions
providing hierarchy, and "graph" regions being like DSGs. Significant
differences include:

- MLIR uses names everywhere, which internally are mapped to some kind
  of hyperedge; we have explicit edges in the structure.
  - However, we can think of every output nodeport being a unique
    SSA/SSI name.
  - MLIR does not do linearity or SSI.
- Our CFGs are Single Entry Single Exit (results defined by the output
  node of the exit block), rather than MLIR's Single Entry Multiple
  Exit (with `return` instruction)
- MLIR allows multiple regions inside a single operation, whereas we
  introduce extra levels of hierarchy to allow this.
- I note re. closures that MLIR expects the enclosing scope to make
  sure any referenced values are kept 'live' for long enough. Not what
  we do in Tierkreis (the closure-maker copies them)\!
