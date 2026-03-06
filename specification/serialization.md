# Serialization

## Goals

- Fast serialization/deserialization in Rust.
- Ability to generate and consume from Python.
- Reasonably small sized files/payloads.
- Ability to send over wire. Nexus will need to do things like:
  - Store the program in a database
  - Search the program(?) (Increasingly
    unlikely with larger more complicated programs)
  - Validate the data
  - **Most important:** version the data for compiler/runtime
    compatibility

## Non-goals

Human-programmability: LLVM for example has exact correspondence between
it's bitcode, in memory and human readable forms. This is quite handy
for developers to inspect and modify the human readable form directly.
Unfortunately this then requires a grammar and parsing/codegen, which is
maintenance and design overhead. We believe that for most cases,
inspecting and modifying the in-memory structure will be enough. If not,
in future we can add a human language and a standalone module for
conversion to/from the binary serialized form.

## Schema

We propose the following simple serialized structure, expressed here in
pseudocode, though we advocate MessagePack format in practice (see
[JSON schema documentation](json-schema/serialization.md)).
Note in particular that hierarchical relationships
have a special encoding outside `edges`, as a field `parent`
in a node definition. Nodes are identified by their position in the `nodes`
list, starting from 0. The unique root node of the HUGR reports itself as the
parent.

The other required field in a node is `op` which identifies an operation by
name, and is used as a discriminating tag in validating the remaining fields.
The other fields are defining data for the particular operation, including
`params` which specifies the arguments to the `TypeParam`s of the operation.
Metadata could also be included as a map keyed by node index.

```rust
struct HUGR {
  nodes: [Node],
  edges: [Edge],
}

struct Node{
  // parent node index
  parent: Int,
  // name of operation
  op: String
  //other op-specific fields
  ...
}
// ((source, offset), (target, offset)
struct Edge = ((Int, Optional<Int>), (Int, Optional<Int>))
```

Node indices, used within the
definitions of nodes and edges, directly correspond to positions in the
`nodes` list. An edge is defined by the source and target nodes, and
optionally the offset of the output/input ports within those nodes, if the edge
kind is one that connects to a port. This scheme
enforces that nodes are contiguous - a node index must always point to a
valid node - whereas in tooling implementations it may be necessary to
implement stable indexing where removing a node invalidates that index
while keeping all other indices pointing to the same node.

Nodes with `Input` and `Output` children are expected to appear earlier in the
list than those children, and `Input` nodes should appear before their matching
`Output` nodes.
