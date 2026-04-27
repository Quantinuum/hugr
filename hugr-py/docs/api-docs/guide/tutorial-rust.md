# HUGR Rust tutorial

As an introduction to working with the `hugr` crate to build HUGRs, we'll
construct a series of example programs of increasing complexity.

Our first example is a simple classical program that increments an integer. Even
this example involves a fair amount of complexity. We'll have to explicitly
include the `arithmetic.int` extension.

For our next example we'll construct a HUGR that just prepares a Bell state on
two qubits. For this we'll need the `tket.quantum` extension defined in the
`tket` crate.
