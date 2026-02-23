# Glossary

- **BasicBlock node**: A child of a CFG node (i.e. a basic block
  within a control-flow graph).
- **Call node**: TODO
- **child node**: A child of a node is an adjacent node in the
  hierarchy that is further from the root node; equivalently, the
  target of a hierarchy edge from the current (parent) node.
- **const edge**: TODO
- **const node**: TODO
- **container node**: TODO
- **control-flow edge**: An edge between BasicBlock nodes in the same
  CFG (i.e. having the same parent CFG node).
- **control-flow graph (CFG)**: The set of all children of a given CFG
  node, with all the edges between them. Includes exactly one entry
  and one exit node. Nodes are basic blocks, edges point to possible
  successors.
- **Dataflow edge** either a `Value` edge or a Static edge; has a type,
  and runs between an output port and an input port.
- **Dataflow Sibling Graph (DSG)**: The set of all children of a given
  Dataflow container node, with all edges between them. Includes
  exactly one input node (unique node having no input edges) and one
  output node (unique node having no output edges). Nodes are
  processes that operate on input data and produce output data. Edges
  in a DSG are either value or order edges. The DSG must be acyclic.
- **data-dependency node**: an input, output, operation, DFG, CFG,
  Conditional or TailLoop node. All incoming and outgoing edges are
  value edges.
- **FuncDecl node**: child of a module, indicates that an external
  function exists but without giving a definition. May be the source
  of `Function`-edges to Call nodes.
- **FuncDefn node**: child of a module node, defines a function (by being
  parent to the function's body). May be the source of `Function`-edges
  to Call nodes.
- **DFG node**: A node representing a data-flow graph. Its children
  are all data-dependency nodes.
- **edge kind**: There are six kinds of edge: `Value` edge, order edge, hierarchy edge,
  control-flow edge, `Const` edge and `Function` edge.
- **edge type:** Typing information attached to a value edge or Static
  edge (representing the data type of value that the edge carries).
- **entry node**: The distinguished node of a CFG representing the
  point where execution begins.
- **exit node**: The distinguished node of a CFG representing the
  point where execution ends.
- **function:** TODO
- **Conditional node:** TODO
- **hierarchy**: A tree whose nodes comprise all nodes of the HUGR,
  rooted at the HUGR's root node.
- **hierarchy edge**: An edge in the hierarchy tree. The edge is considered to
  be directed, with the source node the parent of the target node.
- **input node**: The distinguished node of a DSG representing the
  point where data processing begins.
- **input signature**: The input signature of a node is the mapping
  from identifiers of input ports to their associated edge types.
- **Inter-graph Edge**: Deprecated, see *non-local edge*
- **CFG node**: A node representing a control-flow graph. Its children
  are all BasicBlock nodes, of which there is exactly one entry node
  and exactly one exit node.
- **load-constant node**: TODO
- **metadata:** TODO
- **module**: TODO
- **node index**: An identifier for a node that is unique within the
  HUGR.
- **non-local edge**: A Value or Static edge with Locality Ext,
  or a Value edge with locality Dom (i.e. not Local)
- **operation**: TODO
- **output node**: The distinguished node of a DSG representing the
  point where data processing ends.
- **output signature**: The output signature of a node is the mapping
  from identifiers of output ports to their associated edge types.
- **parent node**: The parent of a non-root node is the adjacent node
  in the hierarchy that is nearer to the root node.
- **port**: A notional entry or exit point from a data-dependency
  node, which has an identifier that is unique for the given node.
  Each incoming or outgoing value edge is associated with a specific
  port.
- **port index**: An identifier for a port that is unique within the
  HUGR.
- **replacement**: TODO
- **extension**: TODO
- **sibling graph**: TODO
- **signature**: The signature of a node is the combination of its
  input and output signatures.
- **simple type**: a quantum or classical type annotated with the
  Extensions required to produce the value
- **Static edge**: either a `Const` or `Function` edge
- **order edge**: An edge implying dependency of the target node on
  the source node.
- **TailLoop node**: TODO
- **value edge:** An edge between data-dependency nodes. Has a fixed
  edge type.
