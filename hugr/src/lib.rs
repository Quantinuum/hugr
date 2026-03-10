//! Extensible, graph-based program representation with first-class support for linear types.
//!
//! The name HUGR stands for "Hierarchical Unified Graph Representation". It is designed primarily
//! as an intermediate representation and interchange format for quantum and hybrid
//! classical–quantum programs.
//!
//! Both data-flow and control-flow graphs can be represented in the HUGR. Nodes in the graph may
//! represent basic operations, or may themselves have "child" graphs, which inherit their inputs
//! and outputs. Special "non-local" edges allow data to pass directly from a node to another node
//! that is not a direct descendent (subject to causality constraints).
//!
//! The specification can be found
//! [here](https://quantinuum.github.io/hugr/specification/index.html).
//!
//! This crate provides a Rust implementation of HUGR and the standard extensions defined in the
//! specification.
//!
//! It includes methods for:
//!
//! - building HUGRs from basic operations;
//! - defining new extensions;
//! - serializing and deserializing HUGRs;
//! - performing local rewrites.
//!
//! # Example
//!
//! Here we build a simple HUGR representing a boolean circuit using the [[`builder::DFGBuilder`]] as follows:
//! ```
//! use hugr::builder::{BuildError, DFGBuilder, Dataflow, DataflowHugr, inout_sig};
//! use hugr::extension::prelude::{bool_t};
//! use hugr::envelope::EnvelopeConfig;
//! use hugr::hugr::Hugr;
//! use hugr::ops::Value;
//! use hugr::std_extensions::logic::LogicOp;
//!
//!
//! fn make_dfg_hugr() -> Result<Hugr, BuildError> {
//!     // pseudocode:
//!     // input x0
//!     // x1 == not(true)
//!     // x2 := not(x0)
//!     // x3 := or(x0,x2)
//!     // x4 := and(x1,x3)
//!     // output x4
//!     let mut dfg_builder = DFGBuilder::new(inout_sig(
//!         vec![bool_t()],
//!         vec![bool_t()],
//!     ))?;
//!
//!     let [x0] = dfg_builder.input_wires_arr();
//!     let true_val = dfg_builder.add_load_value(Value::true_val());
//!     let x1 = dfg_builder.add_dataflow_op(LogicOp::Not, [true_val]).unwrap();
//!     let x2  = dfg_builder.add_dataflow_op(LogicOp::Not, [x0]).unwrap();
//!     let x3 = dfg_builder.add_dataflow_op(LogicOp::Or, [x0, x2.out_wire(0)]).unwrap();
//!     let x4 = dfg_builder.add_dataflow_op(LogicOp::And, x1.outputs().chain(x3.outputs())).unwrap();
//!
//!     dfg_builder.finish_hugr_with_outputs(x4.outputs())
//! }
//!
//! let h: Hugr = make_dfg_hugr().expect("build hugr");
//! // Serialize the hugr to obtain a printable representation
//! let serialized = h.store_str(EnvelopeConfig::text()).expect("serialize");
//! println!("{}", serialized);
//!
//! ```
//!
//! Natively, HUGR does not include any quantum operations, but it is possible to define
//! a quantum extension and then use it to build a HUGR.
//! See the documentation in the [extension module](extension) for an example of a simple quantum extension.

// These modules are re-exported as-is. If more control is needed, define a new module in this crate with the desired exports.
// The doc inline directive is necessary for renamed modules to appear as if they were defined in this crate.
pub use hugr_core::{
    builder, core, envelope, extension, metadata, ops, package, std_extensions, types, utils,
};

#[cfg(feature = "llvm")]
#[doc(inline)]
pub use hugr_llvm as llvm;

#[cfg(feature = "persistent_unstable")]
#[doc(hidden)] // TODO: remove when stable
pub use hugr_persistent as persistent;

// Modules with hand-picked re-exports.
pub mod hugr;

// Top-level re-exports for convenience.
pub use hugr_core::core::{
    CircuitUnit, Direction, IncomingPort, Node, NodeIndex, OutgoingPort, Port, PortIndex, Wire,
};
pub use hugr_core::extension::Extension;
pub use hugr_core::hugr::{Hugr, HugrView, SimpleReplacement};

// Re-export macros.
pub use hugr_core::macros::{const_extension_ids, type_row};
