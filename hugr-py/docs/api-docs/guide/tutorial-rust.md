# HUGR Rust tutorial

As an introduction to working with the `hugr` crate to build HUGRs, we'll
construct a series of example programs of increasing complexity.

Our first example is a simple classical program that increments an integer. Even
this example involves a fair amount of complexity. We'll have to explicitly
include the `arithmetic.int` extension.

```rs
use hugr::{
    builder::{Container, DFGBuilder, Dataflow, DataflowHugr},
    envelope::EnvelopeConfig,
    ops::Value,
    std_extensions::arithmetic::{
        int_ops::IntOpDef,
        int_types::{ConstInt, int_type},
    },
    types::Signature,
};

fn main() {
    // Set up a DFG (dataflow graph) builder. We have to specify the signature:
    // a vector of input types and a vector of output types. In this case, there
    // is a 64-bit integer input and output. The type for a 64-bit integer is
    // specified as `int_type(6)` because 64 = 2^6. Integer widths of all power-
    // -of-2 widths from 1 to 64 are supported.
    let mut dfg_builder =
        DFGBuilder::new(Signature::new(vec![int_type(6)], vec![int_type(6)])).unwrap();

    // Get a handle to the single input wire.
    let [input_wire] = dfg_builder.input_wires_arr();

    // Define the i64 constant value 1.
    let const_i64_1 = ConstInt::new_s(6, 1).unwrap();

    // Prepare to add a `Const` node holding this value.
    let const_node_id = dfg_builder.add_constant(Value::from(const_i64_1));

    // Add the `Const` and `LoadConstant` nodes, getting the output wire.
    let const_wire = dfg_builder.load_const(&const_node_id);

    // Add an operation to add the values on the input wire and the wire from
    // the `LoadConstant`.
    let add1 = dfg_builder
        .add_dataflow_op(IntOpDef::iadd.with_log_width(6), [input_wire, const_wire])
        .unwrap();

    // Finish building the DFG and wrap it in a function definition at the top
    // level of a HUGR module.
    let hugr = dfg_builder
        .finish_hugr_with_outputs(add1.outputs())
        .unwrap();

    // Print a textual representation of the result.
    print!("{}", hugr.store_str(EnvelopeConfig::text()).unwrap());
}
```

This program prints the following:

```
HUGRiHJv)@[](hugr 0)

(mod)

(import core.title)

(import core.fn)

(import arithmetic.int.const)

(import core.entrypoint)

(import core.load_const)

(import core.nat)

(import core.meta.description)

(import arithmetic.int.types.int)

(declare-operation
  arithmetic.int.iadd
  (param ?_0 core.nat)
  (core.fn
    [(arithmetic.int.types.int ?_0) (arithmetic.int.types.int ?_0)]
    [(arithmetic.int.types.int ?_0)])
  (meta
    (core.meta.description
      "addition modulo 2^N (signed and unsigned versions are the same op)")))

(define-func
  private
  _1
  (core.fn [(arithmetic.int.types.int 6)] [(arithmetic.int.types.int 6)])
  (meta (core.title "main"))
  (dfg [%0] [%1]
    (signature
      (core.fn [(arithmetic.int.types.int 6)] [(arithmetic.int.types.int 6)]))
    (dfg [%0] [%1]
      (signature
        (core.fn [(arithmetic.int.types.int 6)] [(arithmetic.int.types.int 6)]))
      (meta core.entrypoint)
      (dfg [%2] [%3]
        (signature
          (core.fn
            [(arithmetic.int.types.int 6)]
            [(arithmetic.int.types.int 6)]))
        ((core.load_const (arithmetic.int.const 6 1)) [] [%4]
          (signature (core.fn [] [(arithmetic.int.types.int 6)])))
        ((arithmetic.int.iadd 6) [%2 %4] [%3]
          (signature
            (core.fn
              [(arithmetic.int.types.int 6) (arithmetic.int.types.int 6)]
              [(arithmetic.int.types.int 6)])))))))
```

The first ten characters (`HUGRiHJv)@`) specify the "envelope format". A few
different formats are supported for HUGR serialization; the serialized bytes
always begin with ten characters that identify the format of the remaining
bytes. In this case we have used `EnvelopeConfig::text()` which gives a fairly
readable representation of the structure.

For our next example we'll construct a HUGR that just prepares a Bell state on
two qubits. For this we'll need the `tket.quantum` extension defined in the
`tket` crate.
