# Appendix: Node types and their edges

The following table shows which edge kinds may adjoin each node type.

Under each edge kind, the inbound constraints are followed by the outbound
constraints. The symbol ✱ stands for "any number", while + stands for "at least
one". For example, "1, ✱" means "one edge in, any number out".

The "Root" row of the table applies to whichever node is the HUGR root,
including `Module`.

| Node type      | `Value` | `Order` | `Const` | `Function` | `ControlFlow` | `Hierarchy` | Children |
|----------------|---------|---------|---------|------------|---------------|-------------|----------|
| Root           | 0, 0    | 0, 0    | 0, 0    | 0, 0       | 0, 0          | 0, ✱        |          |
| `FuncDefn`     | 0, 0    | 0, 0    | 0, 0    | 0, ✱       | 0, 0          | 1, +        | DSG      |
| `FuncDecl`     | 0, 0    | 0, 0    | 0, 0    | 0, ✱       | 0, 0          | 1, 0        |          |
| `AliasDefn`    | 0, 0    | 0, 0    | 0, 0    | 0, 0       | 0, 0          | 1, 0        |          |
| `AliasDecl`    | 0, 0    | 0, 0    | 0, 0    | 0, 0       | 0, 0          | 1, 0        |          |
| `Const`        | 0, 0    | 0, 0    | 0, ✱    | 0, 0       | 0, 0          | 1, 0        |          |
| `LoadConstant` | 0, 1    | ✱, ✱    | 1, 0    | 0, 0       | 0, 0          | 1, 0        |          |
| `LoadFunction` | 0, 1    | ✱, ✱    | 0, 0    | 1, 0       | 0, 0          | 1, 0        |          |
| `Input`        | 0, ✱    | 0, ✱    | 0, 0    | 0, 0       | 0, 0          | 1, 0        |          |
| `Output`       | ✱, 0    | ✱, 0    | 0, 0    | 0, 0       | 0, 0          | 1, 0        |          |
| `Call`         | ✱, ✱    | ✱, ✱    | 0, 0    | 1, 0       | 0, 0          | 1, 0        |          |
| `DFG`          | ✱, ✱    | ✱, ✱    | 0, 0    | 0, 0       | 0, 0          | 1, +        | DSG      |
| `CFG`          | ✱, ✱    | ✱, ✱    | 0, 0    | 0, 0       | 0, 0          | 1, +        | CSG      |
| `DFB`          | 0, 0    | 0, 0    | 0, 0    | 0, 0       | ✱, ✱          | 1, +        | DSG      |
| `Exit`         | 0, 0    | 0, 0    | 0, 0    | 0, 0       | +, 0          | 1, 0        |          |
| `TailLoop`     | ✱, ✱    | ✱, ✱    | 0, 0    | 0, 0       | 0, 0          | 1, +        | DSG      |
| `Conditional`  | ✱, ✱    | ✱, ✱    | 0, 0    | 0, 0       | 0, 0          | 1, +        | `Case`   |
| `Case`         | 0, 0    | 0, 0    | 0, 0    | 0, 0       | 0, 0          | 1, +        | DSG      |
| `CustomOp`     | ✱, ✱    | ✱, ✱    | 0, 0    | 0, 0       | 0, 0          | 1, 0        |          |
| `Noop`         | 1, 1    | ✱, ✱    | 0, 0    | 0, 0       | 0, 0          | 1, 0        |          |
| `MakeTuple`    | ✱, 1    | ✱, ✱    | 0, 0    | 0, 0       | 0, 0          | 1, 0        |          |
| `UnpackTuple`  | 1, ✱    | ✱, ✱    | 0, 0    | 0, 0       | 0, 0          | 1, 0        |          |
| `Tag`          | 1, 1    | ✱, ✱    | 0, 0    | 0, 0       | 0, 0          | 1, 0        |          |
| `Lift`         | ✱, ✱    | ✱, ✱    | 0, 0    | 0, 0       | 0, 0          | 1, 0        |          |
