//! Compilation passes acting on the HUGR program representation.

pub mod composable;
pub mod const_fold;
pub mod dataflow;
pub mod dead_code;
pub mod force_order;
pub mod inline_dfgs;
pub mod inline_funcs;
pub mod lower;
pub mod nest_cfgs;
pub mod non_local;
pub mod normalize_cfgs;
pub mod redundant_order_edges;
pub mod replace_types;
pub mod untuple;

mod dead_funcs;
mod half_node;
mod monomorphize;

// Main pass interfaces
pub use composable::{ComposablePass, InScope, PassScope};

// Pass re-exports
pub use dead_code::DeadCodeElimPass;
#[deprecated(note = "Use RemoveDeadFuncsPass instead")]
#[expect(deprecated)] // Remove together
pub use dead_funcs::remove_dead_funcs;
pub use dead_funcs::{RemoveDeadFuncsError, RemoveDeadFuncsPass, remove_dead_funcs_scoped};
pub use force_order::{force_order, force_order_by_key};
pub use inline_funcs::inline_acyclic;
pub use lower::{lower_ops, replace_many_ops};
pub use monomorphize::{MonomorphizePass, mangle_name, monomorphize};
pub use non_local::{ensure_no_nonlocal_edges, nonlocal_edges};
pub use replace_types::ReplaceTypes;
pub use untuple::UntuplePass;
