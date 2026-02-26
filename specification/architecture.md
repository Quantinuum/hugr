# Architecture

The HUGR is implemented as a Rust crate named `hugr`. This
crate is intended to be a common dependency for all projects, and is published
at the [crates.io registry](https://crates.io/crates/hugr).

The HUGR is represented internally using structures from the `portgraph`
crate. A base PortGraph is composed with hierarchy (as an alternate
implementation of `Hierarchy` relationships) and weight components. The
implementation of this design document is [available on GitHub](https://github.com/quantinuum/hugr).
