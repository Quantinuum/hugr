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

/// Try to produce a human-readable name from an internal HUGR function name.
///
/// We expect a "mangled" name in the following form:
/// `__hugr__.<Python module>.<guppy identifier>.<node ID>`, where the Guppy
/// identifier can be a Python identifier path with multiple dot components.
///
/// The pretty name is obtained by removing the first two dot components (`__hugr__` and
/// the Python module) and the final dot component (the node ID).  If there are not
/// enough dot components to do this (fewer than three dots total), the original name is
/// returned unchanged.
fn unmangle_hugr_func_name(name: &str) -> &str {
    // Index of the dot that starts the third component (after __hugr__ and module).
    let Some(lpar) = name.match_indices('.').nth(1).map(|(i, _)| i) else {
        return name;
    };
    // Index of the last dot (separates the guppy identifier from the node ID).
    // `unwrap` is safe: we already know there are at least two dots.
    let rpar = name.rfind('.').unwrap();
    if lpar < rpar {
        &name[(lpar + 1)..rpar]
    } else {
        name
    }
}

/// This type wraps the Inkwell DebugInfoBuilder and is responsible for converting HUGR
/// debug info into the format expected by Inkwell/LLVM.
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
    // TODO: replace this with HUGR debug types after second milestone
    /// Fixed opaque pointer type
    ptr_type: DIType<'c>,
    /// Placeholder DIFile for compiler-generated code
    compgen_file: DIFile<'c>,
    /// Counts the number of compiler-generated functions so far,
    /// used to give each one a unique location record
    num_compgen: u32,
    // NOTE: have_di_loc may not match the Builder's view of things,
    // see: https://github.com/TheDan64/inkwell/issues/674
    /// Tracks whether the builder currently has a location set
    have_di_loc: bool,
}

impl<'c> DebugInfoContext<'c> {
    /// If there is a compilation unit record attached to the HUGR Module,
    /// create and return Some(DebugInfoContext). If there is
    /// a different debug record attached, return Err.
    /// Otherwise, return Ok(None).
    pub fn try_from_hugr_module<H: HugrView<Node = Node>>(
        node: FatNode<'_, hugr_core::ops::Module, H>,
        iw_module: &Module<'c>,
        ptr_bits: u32,
    ) -> Result<Option<Self>> {
        let maybe_record = try_get_debug_meta::<_, CompileUnitRecord>(node.hugr(), node.node())?;
        let Some(root_meta) = maybe_record else {
            return Ok(None);
        };

        // LLVM debug info version
        let di_version = iw_module.get_context().i32_type().const_int(3, false);
        iw_module.add_basic_value_flag("Debug Info Version", FlagBehavior::Warning, di_version);

        let prod_str = node
            .hugr()
            .get_metadata::<HugrGenerator>(node.node())
            .map(|genmeta| genmeta.to_string())
            .unwrap_or("unknown_hugr_generator".to_string());

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
                // TODO: parse directory? relative paths?
                |path| builder.create_file(path, ""),
            )
            .collect();

        // NOTE: LLVM has purpose-built constructs to represent this
        // (DebugLoc::getCompilerGenerated etc), but they are not exposed
        // through the C API. Internally they appear to just be records with null
        // metadata ptrs, but Inkwell doesn't seem to let us construct those either.
        let compgen_file = builder.create_file("COMPILER_GENERATED_CODE", "");

        // note that this is not a DIPointerType, because
        // it should be void* but Inkwell may not support creating a void DIType
        let ptr_type = builder
            .create_basic_type("ptr", ptr_bits as u64, DWARFTypeCode::Address as u32, 0)?
            .as_type();

        Ok(Some(Self {
            builder,
            compile_unit,
            file_table,
            type_map: BTreeMap::new(),
            fn_type_map: BTreeMap::new(),
            ptr_type,
            compgen_file,
            num_compgen: 0,
            have_di_loc: false,
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
            BasicTypeEnum::PointerType(_) => self.ptr_type.get_size_in_bits() / 8,
            // TODO: this does not respect inter-member alignment. not that important
            // until we have support for values in debug info.
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
        // TODO: need HUGR type to get information about signedness
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
        let arr_subscripts = 0..arr_len_i64;
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

    /// Get a DWARF type record for a LLVM data type,
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
            BasicMetadataTypeEnum::PointerType(_) => Ok(self.ptr_type),
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

        let name = func
            .get_name()
            .to_str()
            .expect("function names should be valid UTF-8");
        let di_fty = self.create_di_function_type(func.get_type(), file)?;
        let is_local = func.get_linkage() != Linkage::External;

        let pretty_name = unmangle_hugr_func_name(name);

        let di_func = self.builder.create_function(
            self.compile_unit.as_debug_info_scope(),
            pretty_name, // name
            Some(name),  // linkage_name
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
        let Some(record) = maybe_record else {
            return Ok(());
        };

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

    /// Construct and attach a debug info record for a compiler-generated function and
    /// set the location to a special placeholder value. This is needed if `func` calls
    /// inlined functions with attached debug info, otherwise the
    /// callees' debug information will be lost.
    pub fn set_compiler_generated(
        &mut self,
        func: FunctionValue<'c>,
        iw_ctx: &'c Context,
        ir_builder: &Builder,
    ) -> Result<()> {
        self.add_di_func(func, self.compgen_file, 0, 0)?;
        let loc = self.builder.create_debug_location(
            iw_ctx,
            self.num_compgen,
            0,
            func.get_subprogram().unwrap().as_debug_info_scope(),
            None,
        );
        self.set_debug_loc(ir_builder, loc)?;
        self.num_compgen += 1;
        Ok(())
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
        if !self.have_di_loc {
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

/// We test debug info generation by adding random info to all HUGRs generated and compiled for other
/// hugr-llvm tests (see `exec_hugr` and `check_emission`).
#[cfg(any(test, feature = "test-utils"))]
pub mod test {
    use super::*;
    use hugr_core::{
        Hugr, envelope::description::GeneratorDesc, hugr::hugrmut::HugrMut, ops::OpType,
    };
    use rand::{
        RngExt, SeedableRng,
        distr::{Alphabetic, SampleString},
        rngs::SmallRng,
    };

    /// Fixed seed for random debug info
    const RAND_DEBUGINFO_SEED: u64 = 0xfeabfaec;
    /// Maximum length of a randomly-generated path component
    const MAX_RAND_COMPONENT_LEN: usize = 32;
    /// Maximum number of components in a randomly-generated path
    const MAX_RAND_PATH_LEN: usize = 8;
    /// Probability of creating a new random file path for a debug info entry
    const NEW_RAND_FILE_PROB: f64 = 0.1;
    /// Maximum random line number
    const MAX_RAND_LNO: usize = 32768;
    /// Maximum random column number
    const MAX_RAND_COLNO: usize = 512;

    fn rand_path(rng: &mut SmallRng, suffix: &str) -> String {
        let mut s = String::new();
        let ncomp = rng.random_range(1..MAX_RAND_PATH_LEN);
        for _ in 1..ncomp {
            s.push('/');
            let comp_len = rng.random_range(1..MAX_RAND_COMPONENT_LEN);
            s.push_str(&Alphabetic.sample_string(rng, comp_len))
        }
        s.push_str(suffix);
        s
    }

    /// Probabilistically get or create a random file and return its index in file_tab
    fn rand_indexed_file(rng: &mut SmallRng, file_tab: &mut Vec<String>) -> usize {
        if file_tab.is_empty() || rng.random_bool(NEW_RAND_FILE_PROB) {
            let i = file_tab.len();
            file_tab.push(rand_path(rng, ".gpy.py"));
            i
        } else {
            rng.random_range(0..file_tab.len())
        }
    }

    /// Add random, format-appropriate debug info to a node
    fn node_random_debug_info(
        hugr: &mut Hugr,
        node: &Node,
        rng: &mut SmallRng,
        file_tab: &mut Vec<String>,
    ) {
        // the root CompileUnit record is generated last, in the calling function
        match hugr.get_optype(*node) {
            OpType::FuncDefn(_) => {
                let lno = rng.random_range(1..MAX_RAND_LNO);
                hugr.set_metadata::<SubprogramRecord>(
                    *node,
                    SubprogramRecord {
                        file: rand_indexed_file(rng, file_tab),
                        line_no: lno,
                        scope_line: lno + 1,
                    },
                );
            }
            OpType::ExtensionOp(_)
            | OpType::OpaqueOp(_)
            | OpType::Call(_)
            | OpType::CallIndirect(_) => {
                hugr.set_metadata::<LocationRecord>(
                    *node,
                    LocationRecord {
                        column: rng.random_range(1..MAX_RAND_COLNO),
                        line_no: rng.random_range(1..MAX_RAND_LNO),
                    },
                );
            }
            _ => (),
        }
    }

    /// Add random, format-appropriate debug info to a Hugr
    /// This needs to be `pub` for non-crate callers of `emit::test::check_emission`
    pub fn add_random_debug_info(hugr: &mut Hugr) {
        let mut rng = SmallRng::seed_from_u64(RAND_DEBUGINFO_SEED);
        let mut file_tab = Vec::new();
        let root = hugr.module_root();

        let node_vec: Vec<Node> = hugr.nodes().collect();
        for node in node_vec.iter() {
            node_random_debug_info(hugr, node, &mut rng, &mut file_tab);
        }

        // need to populate the root metadata last, since it contains the file table.
        hugr.set_metadata::<CompileUnitRecord>(
            root,
            CompileUnitRecord {
                directory: rand_path(&mut rng, ""),
                filename: rand_indexed_file(&mut rng, &mut file_tab),
                file_table: file_tab,
            },
        );
        // debug info emission requires that a generator string is present
        hugr.set_metadata::<HugrGenerator>(root, GeneratorDesc::new_unversioned("hugr_llvm_test"));
    }

    #[cfg(test)]
    mod tests {
        use super::*;
        use crate::custom::CodegenExtsBuilder;
        use crate::emit::test::{DFGW, Emission, SimpleHugrConfig};
        use crate::test::{TestContext, llvm_ctx};
        use crate::utils::fat::FatExt;
        use hugr_core::HugrView;
        use hugr_core::builder::{Dataflow, DataflowHugr};
        use hugr_core::hugr::hugrmut::HugrMut;
        use hugr_core::metadata::debug_info::DEBUGINFO_META_KEY;
        use hugr_core::std_extensions::STD_REG;
        use hugr_core::std_extensions::arithmetic::int_ops::IntOpDef;
        use hugr_core::std_extensions::arithmetic::int_types::int_type;
        use rstest::rstest;

        /// Build a HUGR with a simple integer add function, with all three supported
        /// debug info record types attached: `CompileUnitRecord` on the module root,
        /// `SubprogramRecord` on the `FuncDefn`, and `LocationRecord` on the `ExtensionOp`.
        fn build_hugr_with_all_debug_info() -> Hugr {
            let int64 = int_type(6);
            let mut hugr = SimpleHugrConfig::new()
                .with_ins([int64.clone(), int64.clone()])
                .with_outs([int64])
                .with_extensions(STD_REG.to_owned())
                .finish(|mut builder: DFGW| {
                    let [a, b] = builder.input_wires_arr();
                    let add = builder
                        .add_dataflow_op(IntOpDef::iadd.with_log_width(6), [a, b])
                        .unwrap();
                    builder.finish_hugr_with_outputs(add.outputs()).unwrap()
                });

            let file_table = vec!["test_source.gpy.py".to_string()];
            let root = hugr.module_root();

            let func_node = hugr
                .children(root)
                .find(|&n| matches!(hugr.get_optype(n), OpType::FuncDefn(_)))
                .unwrap();
            hugr.set_metadata::<SubprogramRecord>(
                func_node,
                SubprogramRecord {
                    file: 0,
                    line_no: 10,
                    scope_line: 10,
                },
            );

            let ext_op_node = hugr
                .nodes()
                .find(|&n| matches!(hugr.get_optype(n), OpType::ExtensionOp(_)))
                .unwrap();
            hugr.set_metadata::<LocationRecord>(
                ext_op_node,
                LocationRecord {
                    line_no: 11,
                    column: 4,
                },
            );

            hugr.set_metadata::<CompileUnitRecord>(
                root,
                CompileUnitRecord {
                    directory: "/test/src".to_string(),
                    filename: 0,
                    file_table,
                },
            );
            hugr.set_metadata::<HugrGenerator>(
                root,
                GeneratorDesc::new_unversioned("hugr_llvm_debug_test"),
            );

            hugr
        }

        /// Test that a HUGR with all debug info record types compiles successfully
        /// when debug info emission is enabled.
        #[rstest]
        fn test_debug_info_enabled(mut llvm_ctx: TestContext) {
            llvm_ctx.add_extensions(CodegenExtsBuilder::add_default_int_extensions);
            let hugr = build_hugr_with_all_debug_info();
            let root = hugr.fat_root().unwrap();
            let emission = Emission::emit_hugr(root, llvm_ctx.get_emit_hugr(), true).unwrap();
            emission.verify().unwrap();
        }

        /// Test that a HUGR with all debug info record types compiles successfully
        /// when debug info emission is disabled.
        #[rstest]
        fn test_debug_info_disabled(mut llvm_ctx: TestContext) {
            llvm_ctx.add_extensions(CodegenExtsBuilder::add_default_int_extensions);
            let hugr = build_hugr_with_all_debug_info();
            let root = hugr.fat_root().unwrap();
            let emission = Emission::emit_hugr(root, llvm_ctx.get_emit_hugr(), false).unwrap();
            emission.verify().unwrap();
        }

        /// Test that compilation fails when a wrong debug info record type is attached
        /// to the Module root node (SubprogramRecord instead of CompileUnitRecord).
        #[rstest]
        fn test_wrong_debug_info_on_module(mut llvm_ctx: TestContext) {
            llvm_ctx.add_extensions(CodegenExtsBuilder::add_default_int_extensions);
            let mut hugr = build_hugr_with_all_debug_info();
            // Replace the correct CompileUnitRecord with a SubprogramRecord
            let root = hugr.module_root();
            hugr.set_metadata::<SubprogramRecord>(
                root,
                SubprogramRecord {
                    file: 0,
                    line_no: 1,
                    scope_line: 1,
                },
            );
            let root = hugr.fat_root().unwrap();
            assert!(Emission::emit_hugr(root, llvm_ctx.get_emit_hugr(), true).is_err());
        }

        /// Test that compilation fails when a wrong debug info record type is attached
        /// to a FuncDefn node (LocationRecord instead of SubprogramRecord).
        #[rstest]
        fn test_wrong_debug_info_on_funcdefn(mut llvm_ctx: TestContext) {
            llvm_ctx.add_extensions(CodegenExtsBuilder::add_default_int_extensions);
            let mut hugr = build_hugr_with_all_debug_info();
            // Replace the correct SubprogramRecord with a LocationRecord
            let root = hugr.module_root();
            let func_node = hugr
                .children(root)
                .find(|&n| matches!(hugr.get_optype(n), OpType::FuncDefn(_)))
                .unwrap();
            hugr.set_metadata::<LocationRecord>(
                func_node,
                LocationRecord {
                    line_no: 1,
                    column: 1,
                },
            );
            let root = hugr.fat_root().unwrap();
            assert!(Emission::emit_hugr(root, llvm_ctx.get_emit_hugr(), true).is_err());
        }

        /// Test that compilation fails when a wrong debug info record type is attached
        /// to an ExtensionOp node (SubprogramRecord instead of LocationRecord).
        #[rstest]
        fn test_wrong_debug_info_on_extension_op(mut llvm_ctx: TestContext) {
            llvm_ctx.add_extensions(CodegenExtsBuilder::add_default_int_extensions);
            let mut hugr = build_hugr_with_all_debug_info();
            // Replace the correct LocationRecord with a SubprogramRecord
            let ext_op_node = hugr
                .nodes()
                .find(|&n| matches!(hugr.get_optype(n), OpType::ExtensionOp(_)))
                .unwrap();
            hugr.set_metadata::<SubprogramRecord>(
                ext_op_node,
                SubprogramRecord {
                    file: 0,
                    line_no: 1,
                    scope_line: 1,
                },
            );
            let root = hugr.fat_root().unwrap();
            assert!(Emission::emit_hugr(root, llvm_ctx.get_emit_hugr(), true).is_err());
        }

        /// Test that compilation fails when invalid JSON (not matching CompileUnitRecord's
        /// schema) is attached to the Module root node.
        #[rstest]
        fn test_invalid_json_on_module(mut llvm_ctx: TestContext) {
            llvm_ctx.add_extensions(CodegenExtsBuilder::add_default_int_extensions);
            let mut hugr = build_hugr_with_all_debug_info();
            let root = hugr.module_root();
            hugr.set_metadata_any(
                root,
                DEBUGINFO_META_KEY,
                serde_json::json!({"not_a_valid_field": true}),
            );
            let root = hugr.fat_root().unwrap();
            assert!(Emission::emit_hugr(root, llvm_ctx.get_emit_hugr(), true).is_err());
        }

        /// Test that compilation fails when invalid JSON (not matching SubprogramRecord's
        /// schema) is attached to a FuncDefn node.
        #[rstest]
        fn test_invalid_json_on_funcdefn(mut llvm_ctx: TestContext) {
            llvm_ctx.add_extensions(CodegenExtsBuilder::add_default_int_extensions);
            let mut hugr = build_hugr_with_all_debug_info();
            let root = hugr.module_root();
            let func_node = hugr
                .children(root)
                .find(|&n| matches!(hugr.get_optype(n), OpType::FuncDefn(_)))
                .unwrap();
            hugr.set_metadata_any(
                func_node,
                DEBUGINFO_META_KEY,
                serde_json::json!({"not_a_valid_field": true}),
            );
            let root = hugr.fat_root().unwrap();
            assert!(Emission::emit_hugr(root, llvm_ctx.get_emit_hugr(), true).is_err());
        }

        /// Test that `unmangle_hugr_func_name` correctly strips the prefix and suffix
        /// components from a well-formed mangled name.
        #[test]
        fn test_unmangle_hugr_func_name_valid() {
            // Basic form: __hugr__.<module>.<ident>.<node_id>
            assert_eq!(
                unmangle_hugr_func_name("__hugr__.my_module.my_func.0"),
                "my_func"
            );
            // Guppy identifier is a dotted path (multiple components between module and node ID)
            assert_eq!(
                unmangle_hugr_func_name("__hugr__.my_module.pkg.subpkg.my_func.0"),
                "pkg.subpkg.my_func"
            );
            // Module name with underscores and digits
            assert_eq!(
                unmangle_hugr_func_name("__hugr__.mod_1.foo.bar.42"),
                "foo.bar"
            );
        }

        /// Test that `unmangle_hugr_func_name` returns the original name unchanged when
        /// the name is not in the expected form, even if it contains dots.
        #[test]
        fn test_unmangle_hugr_func_name_preserves_non_mangled() {
            // No dots at all
            assert_eq!(unmangle_hugr_func_name("plain_name"), "plain_name");
            // Only one dot — not enough components
            assert_eq!(unmangle_hugr_func_name("a.b"), "a.b");
            // Two dots, but the middle section is empty so lpar+1 == rpar
            assert_eq!(unmangle_hugr_func_name("a..b"), "a..b");
            // Exactly two dots — middle slice would be empty (lpar+1 == rpar)
            assert_eq!(unmangle_hugr_func_name("a.b.c"), "a.b.c");
        }

        /// Test that compilation fails when invalid JSON (not matching LocationRecord's
        /// schema) is attached to an ExtensionOp node.
        #[rstest]
        fn test_invalid_json_on_extension_op(mut llvm_ctx: TestContext) {
            llvm_ctx.add_extensions(CodegenExtsBuilder::add_default_int_extensions);
            let mut hugr = build_hugr_with_all_debug_info();
            let ext_op_node = hugr
                .nodes()
                .find(|&n| matches!(hugr.get_optype(n), OpType::ExtensionOp(_)))
                .unwrap();
            hugr.set_metadata_any(
                ext_op_node,
                DEBUGINFO_META_KEY,
                serde_json::json!({"not_a_valid_field": true}),
            );
            let root = hugr.fat_root().unwrap();
            assert!(Emission::emit_hugr(root, llvm_ctx.get_emit_hugr(), true).is_err());
        }
    }
}
