# Serialization

This page describes the HUGR serialization stack at a high level. It is meant
to explain the moving parts and the usual data flow, rather than fully specify
every field in every encoding.

Goals:

- Fast serialization/deserialization in Rust.
- Ability to generate and consume from Python.
- Reasonably small files and payloads.
- Ability to send over the wire.

Non-goals:

- Human-programmability: LLVM, for example, has an exact correspondence between
its bitcode, in-memory representation, and human readable forms. This is quite
handy for developers who want to inspect and modify the human readable form
directly. Unfortunately this then requires a stable grammar, parser, printer,
and maintenance overhead for every source level edit. We believe that for most cases,
inspecting and modifying the in-memory structure will be enough.

## Serialization workflow

The usual serialization path is:

1. A tool builds or receives one or more in-memory HUGRs.
2. The HUGRs are grouped into a package, together with any extension
   definitions that should travel with it.
3. The package is exported into the `hugr-model` representation.
4. The model package is encoded either as a compact Cap'n Proto payload or as a
   textual S-expression/EDN-style payload.
5. The encoded payload is wrapped in a HUGR envelope. The envelope records the
   payload format and optional compression settings.

Loading runs the same steps in reverse:

1. Read the envelope header to discover the payload format and compression.
2. Decode the payload into a `hugr-model` package.
3. Import the model package into runtime HUGRs.
4. Resolve extension references using the packaged extension definitions and any
   extension registry provided by the caller.
5. Validate the resulting package before using it for compilation, execution, or
   further transformation.

The intermediate `hugr-model` representation is a key part of the workflow. It
serves as a conversion layer to keep a stable serialization logic when the
runtime HUGR data structures evolve. It is also a shared component between the
rust and python implementations, so a single source of truth for the model
format can be maintained.

## Serialized HUGR Envelopes and payload formats

Serialized HUGRs are normally stored in an envelope. The envelope begins with a
small header containing:

- a magic number identifying the data as a HUGR envelope,
- the payload format,
- flags, including optional zstd compression.

The payload immediately follows the header. Some envelope formats are ASCII
printable and can be stored as strings; others are binary and should be treated
as bytes.

### Cap'n Proto binary payload

This is the compact binary encoding of `hugr-model`. It is the preferred format
for storage, network transfer, and Rust-to-Rust workflows where speed and size
matter more than readability.

The binary payload stores a versioned `hugr-model` package using a Cap'n Proto
schema. It uses table-style identifiers for modules, regions, nodes, terms, and
links, so references are encoded as numeric IDs rather than as nested objects.

When written through the envelope API, the binary model can appear in two
payload formats:

- `Model`: a Cap'n Proto `hugr-model` payload.
- `ModelWithExtensions`: a Cap'n Proto `hugr-model` payload followed by a
  JSON-encoded extension registry.

`ModelWithExtensions` is the default package format today because decoding a
HUGR requires access to the relevant extension definitions. Bundling
non-standard extensions allows toolchains to share HUGRs without previous
knowledge of all the available extensions.

### Textual EDN payload

The text format is an S-expression/EDN-style rendering of the same
`hugr-model` data. It is intended for debugging, snapshots, tests, and review.
It should be readable enough to understand the shape of a HUGR, but it is not
the primary authoring interface.

The text format has two envelope variants:

- `SExpression`: a textual `hugr-model` package.
- `SExpressionWithExtensions`: JSON-encoded extensions followed by the textual
  `hugr-model` package.

The text representation is useful because it exposes the model concepts
directly: modules, regions, nodes, operations, symbol declarations, terms,
metadata, and links. The parser resolves the text AST into the same table model
used by the binary format.

## The `hugr-model` intermediate serialization format

`hugr-model` is the serialization-oriented representation of HUGR. It sits
between the in-memory HUGR objects and the serialized formats.

The runtime HUGR data structures are optimized for construction, querying, and
transformation. The model data structures are optimized for a stable serialized
shape. Export converts runtime HUGRs into `hugr-model`; import converts
`hugr-model` back into runtime HUGRs using an extension registry.

### Table format

The table format is the resolved model representation used by the binary
encoder. It stores package data in arenas/tables and uses IDs to refer between
objects. For example, a term application points to the node that introduces the
symbol it applies, and regions refer to their child nodes by ID.

This format is convenient for serialization because references are explicit and
compact. It is also the form produced after parsing the text AST.

### AST format

The AST format is the unresolved, text-like representation used by the parser
and printer. It keeps names and syntactic structure close to the textual format.
Resolving the AST produces the table format by assigning IDs, checking scoped
names, and creating implicit imports where required.

The distinction lets the project keep a human-readable format without making
that format the main runtime representation.

## Versioning and migration

There are two relevant versioning layers:

- The envelope format identifies how the payload is encoded.
- The `hugr-model` payload carries the model format version.

Readers check the model version before importing the package. The goal is to
allow compatible readers to reject unsupported future payloads early, while
leaving room for migrations from older model versions.

Extensions have their own versions. A serialized package may include extension
definitions, and decoders may also provide an external extension registry when
loading. The import logic uses those definitions to resolve extension
operations, types, and constants into the runtime representation.

Each reference to an extension operation or type in the encoded HUGR also
includes its extension version. This allows extension migration logic to
incrementally update references to new extension versions.

Migration of old HUGRs should normally be handled by specialized tooling like
the HUGR CLI, rather than by the loader hot path used in compilation and
execution contexts. Users need to define migration paths for their own
extensions.

## JSON schema

The project also includes a deprecated JSON schema for the old HUGR IR. See the
[JSON schema serialization notes](../resources/json-schema/serialization.md).
The old JSON package format is no longer the preferred HUGR serialization
format.

JSON is still used for extension definitions in the current envelope formats
that bundle extensions with the model payload. In those formats, the HUGR itself
is encoded as `hugr-model`, while extension definitions are encoded separately
as JSON.

The deprecated schema represented a HUGR roughly as the following graph-shaped
structure. Note in particular that hierarchical relationships have a special
encoding outside `edges`, as a field `parent` in a node definition. Nodes are
identified by their position in the `nodes` list, starting from 0. The unique
root node of the HUGR reports itself as the parent.

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
