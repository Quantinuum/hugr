#![allow(missing_docs)]
use anyhow::{Result, anyhow};
use std::collections::BTreeMap;
use std::ffi::CString;
use std::ops::Deref;

use hugr_core::{
    HugrView, Node,
    metadata::HugrGenerator,
    metadata::debug_info::{
        CompileUnitRecord, LocationRecord, SubprogramRecord, try_get_debug_meta,
    },
};

use inkwell::{
    builder::Builder,
    context::Context,
    debug_info::{
        AsDIScope, DICompileUnit, DIFile, DILocation, DISubprogram, DISubroutineType, DIType,
        DWARFEmissionKind, DWARFSourceLanguage, DebugInfoBuilder,
    },
    module::{FlagBehavior, Linkage, Module},
    types::{
        ArrayType, BasicMetadataTypeEnum, BasicTypeEnum, FloatType, FunctionType, IntType,
        StructType,
    },
    values::FunctionValue,
};

use crate::utils::fat::FatNode;

// alignment for all types
const DEBUG_TYPE_ALIGNMENT: u32 = 8;
// TODO: get this from TargetMachine
const POINTER_BYTES: u64 = 8;

#[expect(dead_code, reason = "Currently unused types")]
enum DWARFTypeCode {
    // Sourced frpm section 7.8 of the standard (look for the DW_ATE prefix),
    // or alternately llvm-project/llvm/include/llvm/BinaryFormat/Dwarf.def.
    // No idea why these aren't defined on the Rust side, rather annoying.
    Address = 1,
    Boolean = 2,
    Float = 4,
    Signed = 5,
    Unsigned = 7,
}

pub struct DebugInfoContext<'c> {
    /// Debug info builder
    builder: DebugInfoBuilder<'c>,
    /// DWARF record for the root compilation unit (HUGR module)
    compile_unit: DICompileUnit<'c>,
    /// Mapping from file indices to DWARF file records
    file_table: Vec<DIFile<'c>>,
    /// Mapping from basic type names to DWARF type records
    type_map: BTreeMap<CString, DIType<'c>>,
    /// Mapping from function type names to DWARF type records
    fn_type_map: BTreeMap<CString, DISubroutineType<'c>>,
    // NOTE: have_di_loc may not match the Builder's view of things,
    // see: https://github.com/TheDan64/inkwell/issues/674
    /// Tracks whether the builder currently has a location set
    have_di_loc: bool,
    /// Size of a pointer on this architecture
    ptr_size: u64,
}

impl<'c> DebugInfoContext<'c> {
    /// If there is a compilation unit record attached to the HUGR Module,
    /// create and return Some(DebugInfoContext). If there is
    /// a different debug record attached, return Err.
    /// Otherwise, return Ok(None).
    pub fn try_from_hugr_module<H: HugrView<Node = Node>>(
        node: FatNode<'_, hugr_core::ops::Module, H>,
        iw_module: &Module<'c>,
    ) -> Result<Option<Self>> {
        let maybe_record = try_get_debug_meta::<_, CompileUnitRecord>(node.hugr(), node.node())?;
        if maybe_record.is_none() {
            return Ok(None);
        }
        let root_meta = maybe_record.unwrap();

        // TODO: who is using this value?
        let di_version = iw_module.get_context().i32_type().const_int(3, false);
        iw_module.add_basic_value_flag("Debug Info Version", FlagBehavior::Warning, di_version);

        let prod_str = node
            .hugr()
            .get_metadata::<HugrGenerator>(node.node())
            .ok_or(anyhow!("Root node missing generator metadata"))?
            .to_string();

        let (builder, compile_unit) = iw_module.create_debug_info_builder(
            true, // allow_unresolved
            DWARFSourceLanguage::Python,
            &(root_meta.file_table[root_meta.filename]),
            &root_meta.directory,
            &prod_str,
            false, // is_optimized
            "",    // flags
            0,     // runtime_ver
            "",    // split_name
            DWARFEmissionKind::Full,
            0,     // dwo_id
            true,  // split_debug_inlining
            false, // debug_info_for_profiling
            "",    // sysroot
            "",    // sdk
        );

        let file_table: Vec<DIFile<'c>> = root_meta
            .file_table
            .iter()
            .map(
                // TODO: parse directory?
                |path| builder.create_file(path, ""),
            )
            .collect();

        Ok(Some(Self {
            builder,
            compile_unit,
            file_table,
            type_map: BTreeMap::new(),
            fn_type_map: BTreeMap::new(),
            have_di_loc: false,
            ptr_size: POINTER_BYTES, //(iw_module.get_context().ptr_sized_int().get_bit_width() / 8).into()
        }))
    }

    /// Get the size of a BasicTypeEnum
    fn get_basic_type_size(&self, ty: BasicTypeEnum<'c>) -> u64 {
        match ty {
            BasicTypeEnum::ArrayType(array_ty) => {
                array_ty.len() as u64 * self.get_basic_type_size(array_ty.get_element_type())
            }
            BasicTypeEnum::FloatType(float_ty) => (float_ty.get_bit_width() / 8).into(),
            BasicTypeEnum::IntType(int_ty) => (int_ty.get_bit_width() / 8).into(),
            BasicTypeEnum::PointerType(_) => self.ptr_size,
            BasicTypeEnum::StructType(struct_ty) => struct_ty
                .get_field_types_iter()
                .fold(0, |len, elem_ty| len + self.get_basic_type_size(elem_ty)),
            _ => panic!("Unexpected type in `get_basic_type_size`: {ty}"),
        }
    }

    fn get_di_file(&self, idx: usize) -> Result<DIFile<'c>> {
        if idx >= self.file_table.len() {
            Err(anyhow!("No debug file at index {idx}"))
        } else {
            Ok(self.file_table[idx])
        }
    }

    fn create_di_int_type(&mut self, int_ty: IntType<'c>) -> Result<DIType<'c>> {
        let width = int_ty.get_bit_width() as u64;
        let name = format!("i{width}");
        // TODO: how to handle signs
        Ok(self
            .builder
            .create_basic_type(&name, width, DWARFTypeCode::Unsigned as u32, 0)
            .map_err(|e| anyhow!("Could not create int DIType: {e}"))?
            .as_type())
    }

    fn create_di_float_type(&mut self, flt_ty: FloatType<'c>) -> Result<DIType<'c>> {
        let width: u64 = flt_ty.get_bit_width().into();
        let name = format!("f{width}");
        Ok(self
            .builder
            .create_basic_type(name.as_str(), width, DWARFTypeCode::Float as u32, 0)
            .map_err(|e| anyhow!("Could not create float DIType: {e}"))?
            .as_type())
    }

    fn create_di_arr_type(&mut self, arr_ty: ArrayType<'c>) -> Result<DIType<'c>> {
        let elem_di_ty = self.get_basic_di_type(arr_ty.get_element_type().into())?;
        let arr_len = arr_ty.len() as u64;
        let arr_bits: u64 = arr_len * elem_di_ty.get_size_in_bits();
        let arr_len_i64: i64 = arr_len
            .try_into()
            .expect("Arrays should have length < 2^63");
        let arr_subscripts = 0..(arr_len_i64 - 1);
        Ok(self
            .builder
            .create_array_type(
                elem_di_ty,
                arr_bits,
                elem_di_ty.get_align_in_bits(),
                &[arr_subscripts],
            )
            .as_type())
    }

    fn create_di_struct_type(&mut self, struct_ty: StructType<'c>) -> Result<DIType<'c>> {
        let mut struct_len: u64 = 0;
        let mut elem_tys = Vec::default();
        for llvm_ty in struct_ty.get_field_types_iter() {
            elem_tys.push(self.get_basic_di_type(llvm_ty.into())?);
            struct_len += self.get_basic_type_size(llvm_ty);
        }

        Ok(self
            .builder
            .create_struct_type(
                self.compile_unit.as_debug_info_scope(), // all structs have global scope
                struct_ty
                    .print_to_string()
                    .to_str()
                    .expect("type name is utf-8"),
                self.compile_unit.get_file(), // TODO: this is probably supposed to be the decl
                0,                            // line_no
                struct_len,
                DEBUG_TYPE_ALIGNMENT,
                0,    // flags
                None, // derived_from
                &elem_tys,
                0,    // runtime_language // TODO: find this enum
                None, // vtable_holder
                "",   // unique_id
            )
            .as_type())
    }

    /// Get a DWARF type record for context-free LLVM types,
    /// creating it if it does not yet exist.
    fn get_basic_di_type(&mut self, llvm_ty: BasicMetadataTypeEnum<'c>) -> Result<DIType<'c>> {
        let name = llvm_ty.print_to_string();
        if let Some(di_ty) = self.type_map.get(name.deref()) {
            return Ok(*di_ty);
        }

        let new_di_ty = match llvm_ty {
            BasicMetadataTypeEnum::ArrayType(arr_ty) => self.create_di_arr_type(arr_ty),
            BasicMetadataTypeEnum::FloatType(flt_ty) => self.create_di_float_type(flt_ty),
            BasicMetadataTypeEnum::IntType(int_ty) => self.create_di_int_type(int_ty),
            BasicMetadataTypeEnum::StructType(struct_ty) => self.create_di_struct_type(struct_ty),
            _ => Err(anyhow!(
                "Type not supported by get_basic_di_type: {llvm_ty:#}"
            )),
        }?;

        if self
            .type_map
            .insert(name.deref().into(), new_di_ty)
            .is_some()
        {
            Err(anyhow!("Duplicate DI type"))
        } else {
            Ok(new_di_ty)
        }
    }

    fn create_di_function_type(
        &mut self,
        fty: FunctionType<'c>,
        fn_file: DIFile<'c>,
    ) -> Result<DISubroutineType<'c>> {
        let name = fty.print_to_string();
        if let Some(di_fty) = self.fn_type_map.get(name.deref()) {
            return Ok(*di_fty);
        }

        let ret_ty = fty.get_return_type().map_or(Ok(None), |llvm_ty| {
            Some(self.get_basic_di_type(llvm_ty.into())).transpose()
        });
        let arg_tys: Result<Vec<_>> = fty
            .get_param_types()
            .iter()
            .map(|llvm_ty| self.get_basic_di_type(*llvm_ty))
            .collect();
        let new_di_fty =
            self.builder
                .create_subroutine_type(fn_file, ret_ty?, arg_tys?.as_slice(), 0);

        if self
            .fn_type_map
            .insert(name.deref().into(), new_di_fty)
            .is_some()
        {
            Err(anyhow!("Duplicate DI function type"))
        } else {
            Ok(new_di_fty)
        }
    }

    /// Common logic for creating function debug info
    fn add_di_func(
        &mut self,
        func: FunctionValue<'c>,
        file: DIFile<'c>,
        lno: u32,
        scope_lno: u32,
    ) -> Result<()> {
        if func.get_subprogram().is_some() {
            return Err(anyhow!("Function already has debug record!"));
        }

        let name_utf8 = func
            .get_name()
            .to_str()
            .expect("function names should be valid UTF-8");
        let di_fty = self.create_di_function_type(func.get_type(), file)?;
        let is_local = func.get_linkage() != Linkage::External;

        let di_func = self.builder.create_function(
            self.compile_unit.as_debug_info_scope(),
            name_utf8,
            Some(name_utf8), // we expect the name to already be mangled at this point. TODO: None instead?
            file,
            lno,
            di_fty,
            is_local,
            // currently, hugr-llvm erases FuncDecls during lowering,
            // so we will never emit a debug record for a declaration.
            true,
            scope_lno,
            0,
            false,
        );

        func.set_subprogram(di_func);
        println!(
            "SET SUBPROG {:?}->{:?}",
            func.get_name(),
            func.get_subprogram().unwrap()
        );
        Ok(())
    }

    /// If the FuncDefn/FuncDecl node has a HUGR debug record attached,
    /// construct a corresponding DISubprogram and attach it to `llvm_func`.
    /// It can be retrieved by calling `llvm_func.get_subprogram()`.
    /// If no debug record is attached, do nothing.
    pub fn try_add_di_func<H: HugrView<Node = Node>, OT>(
        &mut self,
        node: FatNode<'_, OT, H>,
        func: FunctionValue<'c>,
    ) -> Result<()> {
        let maybe_record = try_get_debug_meta::<_, SubprogramRecord>(node.hugr(), node.node())
            .map_err(|e| anyhow!("Could not get subprogram record: {e}"))?;
        if maybe_record.is_none() {
            return Ok(());
        }
        let record = maybe_record.unwrap();

        let di_file = self.get_di_file(record.file)?;
        let lno_u32: u32 = record
            .line_no
            .try_into()
            .map_err(|e| anyhow!("Invalid line_no: {} : {e}", record.line_no))?;
        let scope_lno_u32: u32 = record
            .scope_line
            .try_into()
            .map_err(|e| anyhow!("Invalid scope_line: {} : {e}", record.scope_line))?;
        self.add_di_func(func, di_file, lno_u32, scope_lno_u32)
    }

    /// Construct and attach a debug info record for a stub function,
    /// similar to the above but HUGR debug info is not available
    pub fn try_add_di_stub(&mut self, func: FunctionValue<'c>) -> Result<()> {
        self.add_di_func(func, self.compile_unit.get_file(), 0, 0)
    }

    /// If a node has an attached DILocation record, return Ok(Some(record)).
    /// If the node has other debug info, return Err.
    /// If there is no debug metadata attached, return Ok(None).
    pub fn try_get_di_location<OT, H: HugrView<Node = Node>>(
        &self,
        iw_context: &'c Context,
        node: &FatNode<'_, OT, H>,
        di_func: DISubprogram<'c>,
    ) -> Result<Option<DILocation<'c>>> {
        let maybe_record = try_get_debug_meta::<_, LocationRecord>(node.hugr(), node.node())
            .map_err(|e| anyhow!("Could not get location record: {e}"))?;
        match maybe_record {
            Some(record) => {
                let lno_u32: u32 = record
                    .line_no
                    .try_into()
                    .map_err(|e| anyhow!("Invalid line_no: {} : {e}", record.line_no))?;
                let col_u32: u32 = record
                    .column
                    .try_into()
                    .map_err(|e| anyhow!("Invalid column: {} : {e}", record.column))?;
                Ok(Some(self.builder.create_debug_location(
                    iw_context,
                    lno_u32,
                    col_u32,
                    di_func.as_debug_info_scope(),
                    None,
                )))
            }
            None => Ok(None),
        }
    }

    /// Set the input location record as the IR builder's debug location.
    /// Returns an error if the IR builder already has a debug location.
    pub fn set_debug_loc(&mut self, ir_builder: &Builder, loc: DILocation<'c>) -> Result<()> {
        if self.have_di_loc {
            Err(anyhow!("Debug location is already set"))
        } else {
            ir_builder.set_current_debug_location(loc);
            self.have_di_loc = true;
            Ok(())
        }
    }

    /// Clear the IR builder's current debug location.
    /// Returns an error if the IR builder's debug location is not set.
    pub fn unset_debug_loc(&mut self, ir_builder: &Builder) -> Result<()> {
        if ir_builder.get_current_debug_location().is_none() {
            Err(anyhow!("Debug location is already unset!"))
        } else {
            ir_builder.unset_current_debug_location();
            self.have_di_loc = false;
            Ok(())
        }
    }

    /// Finalize and drop the underlying DebugInfoBuilder
    pub fn finish(self) {
        self.builder.finalize();
    }
}
