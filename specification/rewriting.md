# Replacement and Pattern Matching

We wish to define an API method on the HUGR that allows replacement of a
specified subgraph with a specified replacement graph.

More ambitiously, we also wish to facilitate pattern-matching on the
HUGR.

## Replacement

### Definitions

If n is either a DFG or a CFG node, a set S of nodes in the sibling
graph under n is *convex* (DFG-convex or CFG-convex respectively) if
every node on every path in the sibling graph that starts and ends in S
is itself in S.

The meaning of "convex" is: if A and B are nodes in the convex set S,
then any sibling node on a path from A to B is also in S.

### API methods

There are the following primitive operations.

#### Replacement methods

##### `SimpleReplace`

This method is used for simple replacement of dataflow subgraphs consisting of
leaf nodes. It works by replacing a convex induced subgraph of the main Hugr
with a replacement Hugr having the same signature.

To this end, we specify a `SiblingSubgraph` in terms of a set $X$ of nodes of
the containing Hugr, an input signature $I$ and an output signature $O$. $I$ is
represented as a vector of vectors of input ports of nodes of $X$, where the
outer vector corresponds to the signature and each inner vector corresponds to
one or more copies of a given input into the subgraph (all connected to the
same output port of the containing Hugr). $O$ is represented as a vector of
output ports of nodes in $X$ (possibly with repeats, which correspond to
copies).

Given a `SiblingSubgraph` $S = (X, I, O)$ of a Hugr $H$, and a DFG-rooted Hugr
$H^\prime$ with an input signature matching the outer vector of $I$ and an
output signature matching $O$, we can form a new Hugr by replacing the nodes of
$X$ in $H$ with the Hugr $H^\prime$.

##### `Replace`

This is the general subgraph-replacement method. Intuitively, it takes a set of
sibling nodes to remove and replace with a new set of nodes. The new set of
nodes is itself a HUGR with some "holes" (edges and nodes that get "filled in"
by the `Replace` operation). To fully specify the operation, some further data
are needed:

- The replacement may include container nodes with no children, which adopt
  the children of removed container nodes and prevent those children being
  removed.
- All new incoming edges from the retained nodes to the new nodes, all
  outgoing edges from the new nodes to the retained nodes, and any new edges
  that bypass the replacement (going between retained nodes) must be
  specified.

Given a set $S$ of nodes in a hugr, let $S^\*$ be the set of all nodes
descended from nodes in $S$ (i.e. reachable from $S$ by following hierarchy edges),
including $S$ itself.

A `NewEdgeSpec` specifies an edge inserted between an existing node and a new node.
It contains the following fields:

- `SrcNode`: the source node of the new edge.
- `TgtNode`: the target node of the new edge.
- `EdgeKind`: may be `Value`, `Order`, `Static` or `ControlFlow`.
- `SrcPos`: for `Value` and `Static` edges, the position of the source port;
  for `ControlFlow` edges, the position among the outgoing edges.
- `TgtPos`: (for `Value` and `Static` edges only) the desired position among
  the incoming ports to the new node.

The `Replace` method takes as input:

- the ID of a container node $P$ in $\Gamma$;
- a set $S$ of IDs of nodes that are children of $P$
- a Hugr $G$ whose root is a node of the same type as $P$.
  Note this Hugr need not be valid, in that it may be missing:
  - edges to/from some ports (i.e. it may have unconnected ports)---not just Copyable dataflow outputs, which may occur even in valid Hugrs, but also incoming and/or non-Copyable dataflow ports, and ControlFlow ports,
  - all children for some container nodes strictly beneath the root (i.e. it may have container nodes with no outgoing hierarchy edges)
  - some children of the root, for container nodes that require particular children (e.g.
    $\mathtt{Input}$ and/or $\mathtt{Output}$ if $P$ is a dataflow container, the exit node
    of a CFG, the required number of children of a conditional)
- a map $B$ *from* container nodes in $G$ that have no children *to* container nodes in $S^\*$
  none of which is an ancestor of another.
  Let $X$ be the set of children of nodes in the image of $B$, and $R = S^\* \setminus X^\*$.
- a list $\mu\_\textrm{inp}$ of `NewEdgeSpec` which all have their `TgtNode`in
  $G$ and `SrcNode` in $\Gamma \setminus R$;
- a list $\mu\_\textrm{out}$ of `NewEdgeSpec` which all have their `SrcNode`in
  $G$ and `TgtNode` in $\Gamma \setminus R$, where `TgtNode` and `TgtPos` describe
  an existing incoming edge of that kind from a node in $S^\*$.
- a list $\mu\_\textrm{new}$ of `NewEdgeSpec` which all have both `SrcNode` and `TgtNode`
  in $\Gamma \setminus R$, where `TgtNode` and `TgtPos` describe an existing incoming
  edge of that kind from a node in $S^\*$.

Note that considering all three $\mu$ lists together,

- the `TgtNode` + `TgtPos`s of all `NewEdgeSpec`s with `EdgeKind` == `Value` will be unique
- and similarly for `EdgeKind` == `Static`

The well-formedness requirements of Hugr imply that $\mu\_\textrm{inp}$,
$\mu\_\textrm{out}$ and $\mu\_\textrm{new}$ may only contain `NewEdgeSpec`s with
certain `EdgeKind`s, depending on $P$:

- if $P$ is a dataflow container, `EdgeKind`s may be `Order`, `Value` or `Static` only (no `ControlFlow`)
- if $P$ is a CFG node, `EdgeKind`s may be `ControlFlow`, `Value`, or `Static` only (no `Order`)
- if $P$ is a Module node, there may be `Value` or `Static` only (no `Order`).

(in the case of $P$ being a CFG or Module node, any `Value` edges will be nonlocal, like Static edges.)

The new hugr is then derived as follows:

1. Make a copy in $\Gamma$ of all the nodes in $G$ *except the root*, and all edges except
   hierarchy edges from the root.
2. For each $\sigma\_\mathrm{inp} \in \mu\_\textrm{inp}$, insert a new edge going into the new
   copy of the `TgtNode` of $\sigma\_\mathrm{inp}$ according to the specification $\sigma\_\mathrm{inp}$.
   Where these edges are from ports that currently have edges to nodes in $R$,
   the existing edges are replaced.
3. For each $\sigma\_\mathrm{out} \in \mu\_\textrm{out}$, insert a new edge going out of the new
   copy of the `SrcNode` of $\sigma\_\mathrm{out}$ according to the specification $\sigma\_\mathrm{out}$.
   For `Value` or Static edges, the target port must have an existing edge whose source is in $R$;
   this edge is removed.
4. For each $\sigma\_\mathrm{new} \in \mu\_\textrm{new}$, insert a new edge
   between the existing `SrcNode` and `TgtNode` in $\Gamma$. For `Value` or Static edges,
   the target port must have an existing edge whose source is in $R$; this edge is removed.
5. Let $N$ be the ordered list of the copies made in $\Gamma$ of the children of the root node of $G$.
   For each child $C$ of $P$ (in order), if $C \in S$, redirect the hierarchy edge $P \rightarrow C$ to
   target the next node in $N$. Stop if there are no more nodes in $N$.
   Add any remaining nodes in $N$ to the end of $P$'s list of children.
6. For each node $(n, b = B(n))$ and for each child $m$ of $b$, replace the
   hierarchy edge from $b$ to $m$ with a hierarchy edge from the new copy of
   $n$ to $m$ (preserving the order).
7. Remove all nodes in $R$ and edges adjoining them. (Reindexing may be
   necessary after this step.)

#### Outlining methods

##### `OutlineDFG`

Replace a DFG-convex subgraph with a single DFG node having the original
nodes as children.

##### `OutlineCFG`

Replace a set of CFG sibling nodes with a single BasicBlock node having a
CFG node child which has as its children the set of BasicBlock nodes
originally specified. The set of basic blocks must satisfy constraints:

- There must be at most one node in the set with incoming (controlflow) edges
 from nodes outside the set. Specifically,
  - *either* the set includes the CFG's entry node, and any edges from outside
    the set (there may be none or more) target said entry node;
  - *or* the set does not include the CFG's entry node, but contains exactly one
    node which is the target of at least one edge(s) from outside the set.
- The set may not include the Exit block.
- There must be exactly one edge from a node in the set to a node outside it.

Situations in which multiple nodes have edges leaving the set, or where the Exit block
would be in the set, can be converted to this form by a combination of InsertIdentity
operations and one Replace. For example, rather than moving the Exit block into the nested CFG:

1. An Identity node with a single successor can be added onto each edge into the Exit
2. If there is more than one edge into the Exit, these Identity nodes can then all be combined
   by a Replace operation changing them all for a single Identity (keeping the same number
   of in-edges, but reducing to one out-edge to the Exit).
3. The single edge to the Exit node can then be used as the exiting edge.

#### Inlining methods

These are the exact inverses of the above.

##### `InlineDFG`

Given a DFG node in a DSG, inline its children into the DSG.

##### `InlineCFG`

When a BasicBlock node has a single CFG node as a child, replace it with
the children of that CFG node.

#### Identity insertion and removal methods

##### `InsertIdentity`

Given an edge between sibling nodes in a DSG, insert an `identity<T>`
node having its source as predecessor and its target as successor.

##### `RemoveIdentity`

Remove an `identity<T>` node from a DSG, wiring its predecessor to its
successor.

#### Order insertion and removal methods

##### `InsertOrder`

Insert an Order edge from `n0` to `n1` where `n0` and `n1` are distinct
siblings in a DSG such that there is no path in the DSG from `n1` to
`n0`. (Thus acyclicity is preserved.) If there is already an order edge from
`n0` to `n1` this does nothing (but is not an error).

##### `RemoveOrder`

Given nodes `n0` and `n1`, if there is an Order edge from `n0` to `n1`,
remove it. (If there is an non-local edge from `n0` to a descendent of
`n1`, this invalidates the hugr. **TODO** should this be an error?)

#### Insertion and removal of const loads

##### `InsertConstIgnore`

Given a `Const<T>` node `c`, and optionally `P`, a parent of a DSG, add a new
`LoadConstant<T>` node `n` as a child of `P` with a `Const<T>` edge
from `c` to `n` and no outgoing edges from `n`.  Return the ID of `n`. If `P` is
omitted it defaults to the parent of `c` (in this case said `c` will
have to be in a DSG or CSG rather than under the Module Root.) If `P` is
provided, it must be a descendent of the parent of `c`.

##### `RemoveLoadConstant`

Given a `LoadConstant<T>` node `n` that has no outgoing edges, remove
it (and its incoming Static edge and any Order edges) from the hugr.

#### Insertion and removal of const nodes

##### `InsertConst`

Given a `Const<T>` node `c` and a container node `P` (either a `Module`,
 a `CFG` node or a dataflow container), add `c` as a child of `P`.

##### `RemoveConst`

Given a `Const<T>` node `c` having no outgoing edges, remove `c`.

### Usage

Note that we can only reattach children into empty replacement
containers. This simplifies the API, and is not a serious restriction
since we can use the outlining and inlining methods to target a group of
nodes.

The most basic case -- replacing a convex set of Op nodes in a DSG with
another graph of Op nodes having the same signature -- is implemented by
`SimpleReplace`.

If one of the nodes in the region is a complex container node that we
wish to preserve in the replacement without doing a deep copy, we can
use an empty node in the replacement and have B map this node to the old
one.

We can, for example, implement "turning a Conditional-node with known
Sum into a DFG-node" by a `Replace` where the Conditional (and its
preceding Sum) is replaced by an empty DFG and the map B specifies
the "good" child of the Conditional as the surrogate parent of the new
DFG's children. (If the good child was just an Op, we could either
remove it and include it in the replacement, or -- to avoid this overhead
-- outline it in a DFG first.)

Similarly, replacement of a CFG node having a single BasicBlock child
with a DFG node can be achieved using `Replace` (specifying the
BasicBlock node as the surrogate parent for the new DFG's children).

Arbitrary node insertion on Dataflow edges can be achieved using
`InsertIdentity` followed by `Replace`. Removal of a node in a DSG
having input wires and output wires of the same type can be achieved
using `Replace` (with a set of `identity<T>` nodes) followed by
`RemoveIdentity`.

## Normalisation

We envisage that some kind of pass can be used after a rewrite or series
of rewrites to automatically apply RemoveLoadConstant for any unused
load\_constants, and other such
tidies. This might be global, or by tracking which parts of the Hugr
have been touched.

## Metadata updates on replacement

When requesting a replacement on Γ the caller may optionally provide
metadata for the nodes of Γ and Γ'. Upon replacement, the metadata for
the nodes in Γ are updated with the metadata for the nodes of Γ' that
replace them. (When child nodes are rewired, they keep their existing
metadata.)

The fate of the metadata of nodes in S depends on the policy specified,
as described below.

The caller may also specify a [basic regular
expression](https://en.wikibooks.org/wiki/Regular_Expressions/POSIX_Basic_Regular_Expressions)
(or some other textual pattern format TBD) specifying which keys of
metadata to transfer (e.g. `Foo`, or `*` for all metadata, or `Debug_*`
for all metadata keyed by a string beginning with `Debug_`).

If no policy is specified, the default is to forget all metadata
attached to the replaced subgraph (except for rewired child nodes).

Other policies could include:

- to each of the new nodes added, insert a piece of metadata in its
 `History` section that captures all the chosen metadata with the
 keys of the replaced nodes:
  - `History: {Replaced: [{node1: old_node1_metadata, node2:
    old_node2_metadata, ...}, {...}, ...]}` where `Replaced`
    specifies an ordered list of replacements, and the new
    replacement appends to the list (or creates a new list if
    `Replaced` doesn't yet exist);
- to the root node of Γ, attach metadata capturing a serialization of the
 replacement (both the set of nodes replaced and its replacement):
  - `History: {Replacements: [...]}`

Further policies may be defined in the future; none of these polices
(except for the default forgetful policy) form part of this
specification.

## Pattern matching

We would like to be able to find all subgraphs of a HUGR matching a
given pattern. Exactly how the pattern is specified, and the details of
the algorithm, are not discussed here; but we assume that we have an
implementation of such an algorithm that works on flat
(non-hierarchical) port-graphs.

It can be applied separately to each DSG within the HUGR, matching the
various node types within it. Starting from the root node, we can
recurse down to other DSGs within the HUGR.

It should also be possible to specify a particular DSG on which to run
the pattern matching, by supplying its parent node ID.

Patterns matching edges that traverse DSGs are also possible, but will
be implemented in terms of the above replacement operations, making use
of the child-rewiring lists.
