import tket.extensions as ext
import tket_exts

from hugr import cli, ops, tys
from hugr.build.tracked_dfg import TrackedDfg
from hugr.package import Package

# HUGR extensions needed for this example.
quantum = ext.quantum
measure = ext.measurement

circ = TrackedDfg()

# Retrieve the module from the DFG.
module = circ.module_root_builder()

# Define the quantum functions that will be used within the loop.
with module.define_function("prepare", [tys.Qubit, tys.Qubit]) as prepare:
    # As with other subgraphs, we first retrieve the input wires.
    p_data, p_ancilla = prepare.inputs()
    # Add the operations to the function body.
    p_ancilla = prepare.add(quantum.H(p_ancilla))
    p_data, p_ancilla = prepare.add(quantum.CX(p_data, p_ancilla))
    # As with other subgrapghs, we set the outputs at the end of the function.
    prepare.set_outputs(p_data, p_ancilla)

with module.define_function("correct", [tys.Qubit]) as correct:
    (c_data,) = correct.inputs()
    c_data = correct.add(quantum.X(c_data))
    correct.set_outputs(c_data)

# Then build the tail loop as before.
data = circ.add(quantum.qAlloc())
either_ty = tys.Either([tys.Qubit], [tys.Qubit])

with circ.add_tail_loop([data], []) as loop:
    [loop_data] = loop.inputs()
    ancilla = loop.add(quantum.qAlloc())

    # Instead of adding H and CX operations here, call the "prepare" function.
    # The `FuncDefn` node we need to pass to `call` is always the parent node of
    # the function body.
    loop_data, ancilla = loop.call(prepare.parent_node, loop_data, ancilla)

    measurement = loop.add(quantum.measure_free(ancilla))
    result = loop.add(measure.read(measurement))

    with loop.add_if(result, loop_data) as if_:
        # Instead of adding an X operation here, call the "correct" function.
        flipped = if_.call(correct.parent_node, if_.input_node[0])
        tagged_cont = if_.add(ops.Break(either_ty)(flipped))
        if_.set_outputs(tagged_cont)

    with if_.add_else() as else_:
        tagged_break = else_.add(ops.Continue(either_ty)(else_.input_node[0]))
        else_.set_outputs(tagged_break)

    loop.set_loop_outputs(if_.conditional_node[0])

circ.set_outputs(*loop.outputs())

# Validation and visualisation.
package = Package(modules=[circ.hugr], extensions=tket_exts.tket_registry().extensions)
cli.validate(package.to_bytes())

with open("example-functions1.dot", "w") as f:
    f.write(str(circ.hugr.render_dot()))
