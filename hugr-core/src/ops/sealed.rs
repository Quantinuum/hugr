//! Restricts operation traits to `OpType` and its built-in operation types.
//!
//! Users should use `ExtensionOp` for custom operations.

/// Marks the built-in operation types that may implement the operation traits.
pub trait Sealed {}

impl Sealed for super::AliasDecl {}
impl Sealed for super::AliasDefn {}
impl Sealed for super::Call {}
impl Sealed for super::CallIndirect {}
impl Sealed for super::Case {}
impl Sealed for super::CFG {}
impl Sealed for super::Conditional {}
impl Sealed for super::Const {}
impl Sealed for super::DataflowBlock {}
impl Sealed for super::DFG {}
impl Sealed for super::ExitBlock {}
impl Sealed for super::ExtensionOp {}
impl Sealed for super::FuncDecl {}
impl Sealed for super::FuncDefn {}
impl Sealed for super::Input {}
impl Sealed for super::LoadConstant {}
impl Sealed for super::LoadFunction {}
impl Sealed for super::Module {}
impl Sealed for super::OpaqueOp {}
impl Sealed for super::OpType {}
impl Sealed for super::Output {}
impl Sealed for super::Tag {}
impl Sealed for super::TailLoop {}
