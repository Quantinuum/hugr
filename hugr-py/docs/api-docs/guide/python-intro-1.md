# A Beginner's Guide to Building HUGR Graphs in Python

The goal of this guide is to give a practical introduction to constructing HUGR graphs using the Python interface, demonstrating how various HUGR features lend themselves well to representing quantum algorithms.

## Translating a basic circuit into HUGR

Consider this circuit that constructs a bell pair from two qubits and then measures one of them.

![](images/bell-pair-circuit.png)

It consists of two basic types of components: the wires representing qubit values flowing through the circuit, and quantum operations that can be applied to the wires, representing an action being performed on one or more qubits.

Now let's look at a simple HUGR graph and compare it to the circuit.

A HUGR graph is essentially just a **dataflow graph** (DFG), meaning a graph where nodes are operations and edges represent values flowing from the output of one operation to the input of another, implicitly encoding which computations depend on which other computations. We'll start by initialising a dataflow graph (`Dfg`) with two qubits.

```py
from hugr import tys
from hugr.build.tracked_dfg import TrackedDfg

circ = TrackedDfg(tys.Qubit, tys.Qubit, track_inputs=True)

circ.set_tracked_outputs()
```

The `Tracked` in `TrackedDfg` means we can refer to any tracked wires in the graph by index (as opposed to passing them around directly as we will see in later examples). Even though we are not doing anything in particular with the qubits yet, we need to define the inputs and outputs of the graph. We define the inputs of the graph by passing their types: in this case `Qubit` is available in the built-in `tys` module. The outputs are set by calling `set_tracked_outputs`, which automatically connects all tracked wires to the output node.

Visualising the HUGR results in the following diagram:

![](images/basic1.svg)

> In Python you can visualise HUGRs by using the `render_dot` method.

While we haven't added any nodes to the graph ourselves yet, we can already notice the similarity between dataflow graph edges of type `Qubit` and wires in a circuit both representing qubit values.

However there are also differences - notably, the HUGR consists of multiple **regions**, with each region container having its own input and output nodes. This is where the **hierarchical** part of "Hierarchical Unified Graph Representation" (HUGR) comes from. Certain nodes can themselves contain subgraphs as their children. In our graph we can see some of those nodes:
- The `Module` node is a top-level node which as children can only have function definitions, function declarations, or constants.
- Each module needs at least one function definition that acts as an entrypoint to the graph (however for the module to be executable, the function cannot take any inputs). In this case we have a `FuncDefn` node called `main` by default.
- Finally, the function definition contains the `DFG` we created, so far only containing an input and output node. Note how each port on a node is indexed and ordered.

Let's try to further copy the circuit by adding operations representing quantum gates to the graph, using the `add` method. This requires the use of a HUGR **extension**. An extension is a collection of custom types and operations, in this case `tket.quantum` contains common quantum operations.

```py
import tket.extensions as ext

quantum = ext.quantum

circ.add(quantum.H(0))
circ.add(quantum.CX(0, 1))
```

As this is a DFG with tracked wires, we simply refer to each qubit by its index. The `extend` method lets us add multiple operations at the same time. In this case, after adding a measurement operation on the first qubit, we should also add a `read` operation in order to obtain a `Bool`.

```py
circ.extend(quantum.measure_free(0), measure.read(0))
```

 Connecting the outputs as before with `set_tracked_outputs` to finish, we now get the following graph:

![](images/basic2.svg)

**We now have a HUGR representing the circuit at the start of the guide, with nodes corresponding to gates, and wires corresponding to edges!**

Of course a HUGR is more general than a circuit, with nodes and edges being able to represent various classical values and operations too. For this it is important to know that all nodes and edges are **statically typed**, meaning you can only connect edges to ports with matching types according to the signature of a node.

An important concept for types in HUGR is **linearity**: all types in HUGR are either linear or copyable, where linear values are values that need to be used exactly once so they cannot be dropped or copied (whereas copyable values can be). In graph terms this means that edges of linear types go from exactly one outport to exactly one inport (multuple or no connections are not allowed). This is useful for representing the no-clone and no-delete properties of qubits.

We can demonstrate this concept by looking at the outputs of our DFG. As mentioned before, `set_tracked_outputs` connects all wires to the output automatically. If we instead set the outputs manually by index, we need to be careful to not drop any linear values. So if we connected only the first wire using `circ.set_indexed_outputs(0)` and then tried to validate the resulting HUGR, we would get the following error, as `Qubit` is a linear type:

```
hugr._hugr.model.HugrCliError: Error validating HUGR.

Caused by:
    0: Package validation error.
    1: Node(8) has an unconnected port Port(Outgoing, 1) of type qubit.
```

> You can validate HUGRs either using the CLI tool or by calling `hugr.cli.validate` with a package containing the module you want to check.

If we only connected the second wire with `circ.set_indexed_outputs(1)`, the HUGR would be valid as `Bool` is a copyable type that can be dropped.

> For debugging these kind of validation errors visually, it may be be useful to pass a `RenderConfig` with `display_node_id` set to `True` to `render_dot`.

It was mentioned earlier that for this HUGR to be executable, you need the `main` entrypoint to not have any inputs. Let's do this by allocating the qubits instead. This is also useful for demonstrating how to assign and pass around wires directly instead of using indices, which is useful for the remaining examples (it is also how the Guppy compiler generally handles wires).

First initialise the DFG without any inputs:

```py
circ = TrackedDfg()
```

Then use the `qAlloc` operation to get two qubit wires, and optionally register them as being tracked wires if you still want to refer to them by index (as opposed to using the `q0` and `q1` variables).

```py
q0 = circ.add(quantum.qAlloc()).out(0)
q1 = circ.add(quantum.qAlloc()).out(0)
circ.track_wires([q0, q1])
```

![](images/basic3.svg)

You can find the full example code [here](code/example-basic.py).

## Adding control flow around dynamic measurements

So far all the data in our graph only followed one specific path. What if we now wanted to change the example to do something depending on the outcome of a measurement?

We still start with a `TrackedDfg` with no inputs as before, but then to make it easier to follow what happens with each qubit, let's rename `q0` and `q1` to `data` and `ancilla` and also give the measurement result a name.

```py
data = circ.add(quantum.qAlloc())
ancilla = circ.add(quantum.qAlloc())

ancilla = circ.add(quantum.H(ancilla))
data, ancilla = circ.add(quantum.CX(data, ancilla))

measurement = circ.add(quantum.measure_free(ancilla))
result = circ.add(measure.read(measurement))
```

We then add a **conditional** node (`Conditional`), which creates a new region with subgraphs for each case. We can use `add_if` as a special short hand for a conditional with two cases that branches based on a `Bool` value. In the `True` branch (`result = 1`) we will "correct" the `data` qubit by applying an `X` gate operation, otherwise (`result = 0`) we just pass the qubit back untouched.

```py
with circ.add_if(result, data) as if_:
    flipped = if_.add(quantum.X(if_.input_node[0]))
    if_.set_outputs(flipped)

with if_.add_else() as else_:
    else_.set_outputs(else_.input_node[0])

circ.set_outputs(if_.conditional_node[0])
```

It is possible to not use context managers and instead assign the results of `add_if` and `add_else` to builder variables (and then it is also possible to convert those builders into tracked versions). However using `with` blocks is a useful way of keeping track of the hierarchy, as each block represents a new subgraph inside a node in the dataflow graph, visualised here as new regions:

![](images/control-flow1.svg)

Of course just flipping a qubit isn't a very meaningful thing to do from a quantum perspective, however it showcases the building blocks needed to construct a HUGR in which you first prepare a quantum state and then act on it or correct it based on some ancilla measurement.

Another common scenario is not only branching once, but also repeat-until-success algorithms where we need to prepare a state over and over again until it satisfies a certain condition.

![](images/loop-diagram.png)

This can be represented in HUGR through a **tail loop** node (`TailLoop`).

Tail loops decide whether to keep iterating or exit the loop based on a **sum type** value. Sum types are types whose values belong to exactly one of several variants, with each value consisting of a tag signifying which variant it is, plus whatever data the variant carries. For example, the `Bool` type in HUGR is a sum of two unit variants. More generally, a common sum type is `Either`, with `Left` and `Right` tags which can carry some data. We will use this type as the  condition for our loop, carrying a qubit as data in both cases:

```py
either_ty = tys.Either([tys.Qubit], [tys.Qubit])
```

We can then add the loop node, with the data qubit being allocated once before we start iterating and the ancilla allocation and state preparation happening inside the loop:

```py
data = circ.add(quantum.qAlloc())

with circ.add_tail_loop([data], []) as loop:
    [loop_data] = loop.inputs()
    ancilla = loop.add(quantum.qAlloc())
    ancilla = loop.add(quantum.H(ancilla))
    loop_data, ancilla = loop.add(quantum.CX(loop_data, ancilla))

    measurement = loop.add(quantum.measure_free(ancilla))
    result = loop.add(measure.read(measurement))
```

Then we build the same conditional again, but instead of simply setting the qubit as its output, we tag it by using `Break` or `Continue` operations (which are convenient ways in the standard library for constructing `Right` and `Left` tags):

```py
    with loop.add_if(result, loop_data) as if_:
        flipped = if_.add(quantum.X(if_.input_node[0]))
        tagged_cont = if_.add(ops.Break(either_ty)(flipped))
        if_.set_outputs(tagged_cont)

    with if_.add_else() as else_:
        tagged_break = else_.add(ops.Continue(either_ty)(else_.input_node[0]))
        else_.set_outputs(tagged_break)
```
Finally, set the loop outputs to be the output of the conditional, and the DFG outputs to be the output of the loop and the graph is done!

```py
    loop.set_loop_outputs(if_.conditional_node[0])

circ.set_outputs(*loop.outputs())
```

![](images/control-flow2.svg)

You can find the full example code [here](code/example-control-flow2.py).

## Generalising through functions and polymorphism

As discussed earlier, you might want to generalise the loop we constructed to work for different `prepare` and `correct` sequences. Or you simply don't want have to constantly add the same gate sequences to a graph. The best way to do this is by using **functions**.

Functions can be defined as children of the module node using `define_function`, alongside the `main` function we have already seen. The method takes a function name and type signature and returns a builder we can add nodes to just as we did with DFG, conditional, or loop builders.

Let's put any gates we added in the previous example into two functions instead, `prepare` and `correct`, abstracting them away from the loop logic.

```py
module = circ.module_root_builder()

with module.define_function("prepare", [tys.Qubit, tys.Qubit]) as prepare:
    p_data, p_ancilla = prepare.inputs()
    p_ancilla = prepare.add(quantum.H(p_ancilla))
    p_data, p_ancilla = prepare.add(quantum.CX(p_data, p_ancilla))
    prepare.set_outputs(p_data, p_ancilla)

with module.define_function("correct", [tys.Qubit]) as correct:
    (c_data,) = correct.inputs()
    c_data = correct.add(quantum.X(c_data))
    correct.set_outputs(c_data)
```

Then they can be used inside of the DFG through call nodes. Note that we always require the `FuncDefn` node in order to create a `Call`, which is the parent of the function graph the `define_function` method returns.

```py
...
# Inside the loop builder:
loop_data, ancilla = loop.call(prepare.parent_node, loop_data, ancilla)
...
# Inside the if branch:
flipped = if_.call(correct.parent_node, if_.input_node[0])
...
```

![](images/functions1.svg)

We can use this same pattern to define more complicated and useful preparation and correction gadgets in those functions. One final HUGR feature we will look at in this guide is polymorphism: the ability to define functions that work for different types or parameters.

To demonstrate this, let's add a `correct_all` function which operates on an array of qubits instead of only one qubit and applies a `X` gate to all od them.

[TODO: Finish code, diagram, and text for polymorphic example]

You can see the full example code [here](code/example-functions2.py).
