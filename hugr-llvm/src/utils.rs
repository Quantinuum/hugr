//! Module for utilities that do not depend on LLVM. These are candidates for
//! upstreaming.
pub mod fat;
pub mod int_op_builder;
pub mod logic_op_builder;
pub mod type_map;

pub use int_op_builder::IntOpBuilder;
pub use logic_op_builder::LogicOpBuilder;
