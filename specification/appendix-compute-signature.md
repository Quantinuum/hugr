# Appendix: Binary `compute_signature`

When an OpDef provides a binary `compute_signature` function, and an operation node uses that OpDef:

- the node provides a list of TypeArgs, at least as many as the $n$ TypeParams declared by the OpDef
- the first $n$ of those are passed to the binary `compute_signature`
- if the binary function returns an error, the operation is invalid;
- otherwise, `compute_signature` returns a type scheme (which may itself be polymorphic)
- any remaining TypeArgs in the node (after the first $n$) are then substituted into that returned type scheme
  (the number remaining in the node must match exactly).
  **Note** this allows the binary function to use the values (TypeArgs) passed in---e.g.
  by looking inside `List` or `Opaque` TypeArgs---to determine the structure (and degree of polymorphism) of the returned type scheme.
- We require that the TypeArgs to be passed to `compute_signature` (the first $n$)
  must *not* refer to any type variables (declared by ancestor nodes in the Hugr - the nearest enclosing FuncDefn);
  these first $n$ must be static constants unaffected by substitution.
  This restriction does not apply to TypeArgs after the first $n$.
