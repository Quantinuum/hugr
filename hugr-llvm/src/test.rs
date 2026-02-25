use std::rc::Rc;

use hugr_core::{
    Hugr,
    builder::{Dataflow, DataflowSubContainer, HugrBuilder, ModuleBuilder},
    ops::{OpTrait, OpType},
    types::PolyFuncType,
};
use inkwell::{
    context::Context,
    types::{BasicType, BasicTypeEnum},
};
use itertools::Itertools as _;
use rstest::fixture;

use crate::{
    custom::{CodegenExtsBuilder, CodegenExtsMap},
    emit::{EmitHugr, EmitModuleContext, Namer, test::Emission},
    types::{TypeConverter, TypingSession},
    utils::fat::FatExt as _,
};

pub type THugrView = Hugr;

pub struct InstaSettingsBuilder {
    settings: insta::Settings,
    llvm: Option<String>,
    id: Option<usize>,
    omit_expression: bool,
}

impl InstaSettingsBuilder {
    #[must_use]
    pub fn new_llvm(id: Option<usize>) -> Self {
        let mut r = Self::new(id);
        r.llvm = Some(super::llvm_version().into());
        r
    }

    #[must_use]
    pub fn new(id: Option<usize>) -> Self {
        Self {
            settings: insta::Settings::clone_current(),
            llvm: None,
            id,
            omit_expression: false,
        }
    }

    pub fn settings_mut(&mut self) -> &mut insta::Settings {
        &mut self.settings
    }

    #[must_use]
    pub fn finish(mut self) -> Option<insta::internals::SettingsBindDropGuard> {
        let suffix = self
            .llvm
            .into_iter()
            .chain(self.id.into_iter().map(|x| x.to_string()))
            .join("_");
        self.settings.set_snapshot_suffix(suffix);
        self.settings.set_omit_expression(self.omit_expression);
        Some(self.settings.bind_to_scope())
    }
}

#[must_use]
pub fn no_extensions(id: CodegenExtsMap<'_, THugrView>) -> CodegenExtsMap<'_, THugrView> {
    id
}

pub trait MakeCodegenExtsMapFn:
    Fn(CodegenExtsBuilder<'static, THugrView>) -> CodegenExtsBuilder<'static, THugrView> + 'static
{
}

impl<
    F: Fn(CodegenExtsBuilder<'static, THugrView>) -> CodegenExtsBuilder<'static, THugrView>
        + ?Sized
        + 'static,
> MakeCodegenExtsMapFn for F
{
}

type MakeCodegenExtsMapBox = Box<dyn MakeCodegenExtsMapFn>;
// We would like to just stor a CodegenExtsMap, but we can't because it's
// lifetime parameter would need to be the lifetime of TestContext, which is
// prohibited. Instead, we store a factory function as below.
pub struct TestContext {
    context: Context,
    mk_exts: MakeCodegenExtsMapBox,
    _insta: Option<insta::internals::SettingsBindDropGuard>,
    namer: Namer,
}

impl TestContext {
    fn new(
        ext_builder: impl MakeCodegenExtsMapFn + 'static,
        insta_settings: Option<InstaSettingsBuilder>,
    ) -> Self {
        let context = Context::create();
        Self {
            context,
            mk_exts: Box::new(ext_builder),
            _insta: insta_settings.and_then(InstaSettingsBuilder::finish),
            namer: Default::default(),
        }
    }

    #[must_use]
    pub fn i32(&'_ self) -> BasicTypeEnum<'_> {
        self.context.i32_type().as_basic_type_enum()
    }

    #[must_use]
    pub fn type_converter(&self) -> Rc<TypeConverter<'static>> {
        self.extensions().type_converter
    }

    #[must_use]
    pub fn extensions(&self) -> CodegenExtsMap<'static, THugrView> {
        (self.mk_exts)(Default::default()).finish()
    }

    pub fn add_extensions(&'_ mut self, f: impl MakeCodegenExtsMapFn) {
        let old_mk_exts = {
            let mut tmp: MakeCodegenExtsMapBox = Box::new(|x| x);
            std::mem::swap(&mut self.mk_exts, &mut tmp);
            tmp
        };
        self.mk_exts = Box::new(move |cem| f(old_mk_exts(cem)));
    }

    #[must_use]
    pub fn iw_context(&self) -> &Context {
        &self.context
    }

    #[must_use]
    pub fn get_typing_session(&self) -> TypingSession<'_, 'static> {
        self.type_converter().session(&self.context)
    }

    #[must_use]
    pub fn get_emit_hugr(&'_ self) -> EmitHugr<'_, 'static, THugrView> {
        let ctx = self.iw_context();
        let m = ctx.create_module("test_context");
        let exts = self.extensions();
        EmitHugr::new(ctx, m, Rc::new(self.namer.clone()), Rc::new(exts))
    }

    pub fn set_namer(&mut self, namer: Namer) {
        self.namer = namer;
    }

    #[must_use]
    pub fn get_emit_module_context(&'_ self) -> EmitModuleContext<'_, 'static, THugrView> {
        let ctx = self.iw_context();
        let m = ctx.create_module("test_context");
        EmitModuleContext::new(
            &self.context,
            m,
            self.namer.clone().into(),
            self.extensions().into(),
        )
    }

    /// Lower `hugr` to LLVM, then JIT and execute the function named
    /// by `entry_point` in the inner module.
    ///
    /// That function must take no arguments and return FFI-compatible type `T`.
    pub fn exec_hugr<T>(&self, hugr: THugrView, entry_point: impl AsRef<str>) -> T {
        let emission = Emission::emit_hugr(hugr.fat_root().unwrap(), self.get_emit_hugr()).unwrap();
        emission.verify().unwrap();

        emission.jit_exec::<T>(entry_point).unwrap()
    }

    /// For a given integer size, exec a HUGR returning an integer of that size,
    /// cast the expected value to that size, and assert equality.
    pub fn check_int_hugr(
        &self,
        hugr: THugrView,
        entry_point: impl AsRef<str>,
        log_width: u8,
        expected: u64,
        signed: bool,
    ) {
        // an integer of "log width" N has 2^(2^N) bits
        match (log_width, signed) {
            (0, false) => assert_eq!(self.exec_hugr::<bool>(hugr, entry_point), expected != 0),
            (0, true) => panic!("Signed bool does not exist"),
            // casting to smaller int types in rust is a truncation,
            // plus reinterpret-cast if signedness changes
            (3, true) => assert_eq!(self.exec_hugr::<i8>(hugr, entry_point), expected as i8),
            (3, false) => assert_eq!(self.exec_hugr::<u8>(hugr, entry_point), expected as u8),
            (4, true) => assert_eq!(self.exec_hugr::<i16>(hugr, entry_point), expected as i16),
            (4, false) => assert_eq!(self.exec_hugr::<u16>(hugr, entry_point), expected as u16),
            (5, true) => assert_eq!(self.exec_hugr::<i32>(hugr, entry_point), expected as i32),
            (5, false) => assert_eq!(self.exec_hugr::<u32>(hugr, entry_point), expected as u32),
            // casting to/from signedness in rust is just a reinterpret-cast
            (6, true) => assert_eq!(self.exec_hugr::<i64>(hugr, entry_point), expected as i64),
            (6, false) => assert_eq!(self.exec_hugr::<u64>(hugr, entry_point), expected),
            _ => panic!("Unsupported log width {log_width} for exec_hugr"),
        }
    }

    // legacy wrappers for common types
    pub fn exec_hugr_u64(&self, hugr: THugrView, entry_point: impl AsRef<str>) -> u64 {
        self.exec_hugr::<u64>(hugr, entry_point)
    }

    pub fn exec_hugr_i64(&self, hugr: THugrView, entry_point: impl AsRef<str>) -> i64 {
        self.exec_hugr::<i64>(hugr, entry_point)
    }

    pub fn exec_hugr_f64(&self, hugr: THugrView, entry_point: impl AsRef<str>) -> f64 {
        self.exec_hugr::<f64>(hugr, entry_point)
    }

    /// Lower `hugr` to LLVM, then JIT and execute the function named `entry_point` in the
    /// inner module.
    ///
    /// Takes care of safely handling panics occurring in the program and returns the produced
    /// panic message, or an empty string if no panic occurred.
    ///
    /// For this to work, [`Emission::exec_panicking`] must be used together with the
    /// [`crate::emit::test::PanicTestPreludeCodegen`].
    pub fn exec_hugr_panicking(&self, hugr: THugrView, entry_point: impl AsRef<str>) -> String {
        let emission = Emission::emit_hugr(hugr.fat_root().unwrap(), self.get_emit_hugr()).unwrap();
        emission.verify().unwrap();

        emission.exec_panicking(entry_point).unwrap()
    }
}

#[fixture]
pub fn test_ctx(#[default(-1)] id: i32) -> TestContext {
    let id = (id >= 0).then_some(id as usize);
    TestContext::new(
        |_| CodegenExtsBuilder::default(),
        Some(InstaSettingsBuilder::new(id)),
    )
}

#[fixture]
pub fn llvm_ctx(#[default(-1)] id: i32) -> TestContext {
    let id = (id >= 0).then_some(id as usize);
    TestContext::new(
        |_| CodegenExtsBuilder::default(),
        Some(InstaSettingsBuilder::new_llvm(id)),
    )
}

#[fixture]
pub fn exec_ctx(#[default(-1)] id: i32) -> TestContext {
    let id = (id >= 0).then_some(id as usize);
    let mut r = TestContext::new(
        |_| CodegenExtsBuilder::default(),
        Some(InstaSettingsBuilder::new_llvm(id)),
    );
    // we need to refer to functions by name, so no mangling
    r.set_namer(Namer::new("", false));
    r
}

impl Default for InstaSettingsBuilder {
    fn default() -> Self {
        Self::new_llvm(None)
    }
}

#[must_use]
pub fn single_op_hugr(op: OpType) -> Hugr {
    let Some(sig) = op.dataflow_signature() else {
        panic!("not a dataflow op")
    };
    let sig = sig.into_owned();

    let mut module_builder = ModuleBuilder::new();
    {
        let mut func_builder = module_builder
            .define_function("main", PolyFuncType::from(sig))
            .unwrap();
        let op = func_builder
            .add_dataflow_op(op, func_builder.input_wires())
            .unwrap();
        func_builder.finish_with_outputs(op.outputs()).unwrap()
    };
    module_builder.finish_hugr().unwrap()
}
