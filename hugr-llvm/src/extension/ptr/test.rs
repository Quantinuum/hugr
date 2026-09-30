use super::*;
use crate::{
    emit::{
        EmitDebugInfo,
        test::{Emission, SimpleHugrConfig},
    },
    test::{TestContext, exec_ctx},
    utils::{IntOpBuilder, LogicOpBuilder, fat::FatExt},
};
use hugr_core::{
    Hugr,
    builder::{Dataflow, DataflowHugr, DataflowSubContainer, HugrBuilder},
    extension::prelude::{UnwrapBuilder, bool_t},
    std_extensions::{
        STD_REG,
        arithmetic::int_types::{ConstInt, int_type},
        ptr::PtrOpBuilder,
    },
    types::Type,
};
use inkwell::types::BasicType;
use rstest::rstest;

fn configure(ctx: &mut TestContext) {
    ctx.add_extensions(|b| {
        b.add_default_prelude_extensions()
            .add_default_int_extensions()
            .add_logic_extensions()
            .add_default_ptr_extensions()
    });
}

fn lifecycle() -> Hugr {
    let ty = int_type(6);
    SimpleHugrConfig::new()
        .with_extensions(STD_REG.to_owned())
        .with_outs([bool_t()])
        .finish(|mut b| {
            let one = b.add_load_value(ConstInt::new_u(6, 1).unwrap());
            let two = b.add_load_value(ConstInt::new_u(6, 2).unwrap());
            let three = b.add_load_value(ConstInt::new_u(6, 3).unwrap());
            let ptr = b.add_new_ptr(one).unwrap();
            let (a, other) = b.add_dup_ptr(ptr, ty.clone()).unwrap();
            let a = b.add_write_ptr(a, two).unwrap();
            let (a, read) = b.add_read_ptr(a, ty.clone()).unwrap();
            let (a, old) = b.add_swap_ptr(a, three).unwrap();
            let none = b.add_free_ptr(a, ty.clone()).unwrap();
            b.build_unwrap_sum::<0>(0, option_type([ty.clone()]), none)
                .unwrap();
            let some = b.add_free_ptr(other, ty.clone()).unwrap();
            // The two handles alone do not order their Free operations.
            b.set_order(&none.node(), &some.node());
            let [last] = b.build_unwrap_sum(1, option_type([ty]), some).unwrap();
            let read_ok = b.add_ieq(6, read, two).unwrap();
            let old_ok = b.add_ieq(6, old, two).unwrap();
            let last_ok = b.add_ieq(6, last, three).unwrap();
            let ok = b.add_and(read_ok, old_ok).unwrap();
            let ok = b.add_and(ok, last_ok).unwrap();
            b.finish_hugr_with_outputs([ok]).unwrap()
        })
}

#[rstest]
#[case(false)]
#[case(true)]
fn exec_lifecycle(mut exec_ctx: TestContext, #[case] custom_mutex: bool) {
    configure(&mut exec_ctx);
    if custom_mutex {
        exec_ctx.add_extensions(|b| b.add_ptr_extensions(SpinCodegen));
    }
    assert!(exec_ctx.exec_hugr::<bool>(lifecycle(), "main"));
}

#[rstest]
#[case(false)]
#[case(true)]
fn exec_map(mut exec_ctx: TestContext, #[case] extra: bool) {
    configure(&mut exec_ctx);
    let ty = int_type(6);
    let hugr = SimpleHugrConfig::new()
        .with_extensions(STD_REG.to_owned())
        .with_outs([ty.clone()])
        .finish(|mut b| {
            let mut row = vec![ty.clone()];
            if extra {
                row.push(ty.clone());
            }
            let mut mb = b.module_root_builder();
            let mut callback = mb
                .define_function("update", Signature::new_endo(row))
                .unwrap();
            let ins = callback.input_wires().collect::<Vec<_>>();
            let delta = if extra {
                ins[1]
            } else {
                callback.add_load_value(ConstInt::new_u(6, 4).unwrap())
            };
            let next = callback.add_iadd(6, ins[0], delta).unwrap();
            let out = if extra {
                vec![next, ins[0]]
            } else {
                vec![next]
            };
            let callback = callback.finish_with_outputs(out).unwrap();
            let function = b.load_func(callback.handle(), &[]).unwrap();
            let value = b.add_load_value(ConstInt::new_u(6, 10).unwrap());
            let ptr = b.add_new_ptr(value).unwrap();
            let inputs = if extra {
                vec![b.add_load_value(ConstInt::new_u(6, 4).unwrap())]
            } else {
                vec![]
            };
            let outputs = if extra { vec![ty.clone()] } else { vec![] };
            let (ptr, extras) = b
                .add_map_ptr(ptr, function, ty.clone(), inputs, outputs)
                .unwrap();
            let freed = b.add_free_ptr(ptr, ty.clone()).unwrap();
            let [value] = b.build_unwrap_sum(1, option_type([ty]), freed).unwrap();
            let value = if extra {
                b.add_iadd(6, value, extras[0]).unwrap()
            } else {
                value
            };
            b.finish_hugr_with_outputs([value]).unwrap()
        });
    assert_eq!(
        exec_ctx.exec_hugr_u64(hugr, "main"),
        if extra { 24 } else { 14 }
    );
}

#[rstest]
fn exec_linear_nested_pointer(mut exec_ctx: TestContext) {
    configure(&mut exec_ctx);
    let ty = int_type(6);
    let hugr = SimpleHugrConfig::new()
        .with_extensions(STD_REG.to_owned())
        .with_outs([ty.clone()])
        .finish(|mut b| {
            let value = b.add_load_value(ConstInt::new_u(6, 42).unwrap());
            let inner = b.add_new_ptr(value).unwrap();
            let outer = b.add_new_ptr(inner).unwrap();
            let inner_ty = ptr::ptr_type(ty.clone());
            let outer = b.add_free_ptr(outer, inner_ty.clone()).unwrap();
            let [inner] = b
                .build_unwrap_sum(1, option_type([inner_ty]), outer)
                .unwrap();
            let inner = b.add_free_ptr(inner, ty.clone()).unwrap();
            let [value] = b.build_unwrap_sum(1, option_type([ty]), inner).unwrap();
            b.finish_hugr_with_outputs([value]).unwrap()
        });
    assert_eq!(exec_ctx.exec_hugr_u64(hugr, "main"), 42);
}

#[rstest]
fn exec_zero_sized_value(mut exec_ctx: TestContext) {
    configure(&mut exec_ctx);
    let hugr = SimpleHugrConfig::new()
        .with_extensions(STD_REG.to_owned())
        .finish(|mut b| {
            let unit = b.make_tuple([]).unwrap();
            let ptr = b.add_new_ptr(unit).unwrap();
            let freed = b.add_free_ptr(ptr, Type::UNIT).unwrap();
            b.build_unwrap_sum::<1>(1, option_type([Type::UNIT]), freed)
                .unwrap();
            b.finish_hugr_with_outputs([]).unwrap()
        });
    exec_ctx.exec_hugr::<()>(hugr, "main");
}

fn emit<'c>(ctx: &'c TestContext, hugr: &'c Hugr) -> Emission<'c> {
    let emission = Emission::emit_hugr(
        hugr.fat_root().unwrap(),
        ctx.get_emit_hugr(),
        EmitDebugInfo::Exclude,
    )
    .unwrap();
    emission.verify().unwrap();
    emission
}

#[rstest]
fn exec_map_linear_payload_and_extra(mut exec_ctx: TestContext) {
    configure(&mut exec_ctx);
    let int = int_type(6);
    let inner = ptr::ptr_type(int.clone());
    let hugr = SimpleHugrConfig::new()
        .with_extensions(STD_REG.to_owned())
        .with_outs([int.clone()])
        .finish(|mut b| {
            let mut mb = b.module_root_builder();
            let callback = mb
                .define_function(
                    "exchange",
                    Signature::new_endo([inner.clone(), inner.clone()]),
                )
                .unwrap();
            let [old, new] = callback.input_wires_arr();
            let callback = callback.finish_with_outputs([new, old]).unwrap();
            let function = b.load_func(callback.handle(), &[]).unwrap();
            let a = b.add_load_value(ConstInt::new_u(6, 10).unwrap());
            let c = b.add_load_value(ConstInt::new_u(6, 20).unwrap());
            let a = b.add_new_ptr(a).unwrap();
            let c = b.add_new_ptr(c).unwrap();
            let outer = b.add_new_ptr(a).unwrap();
            let (outer, extra) = b
                .add_map_ptr(outer, function, inner.clone(), [c], [inner.clone()])
                .unwrap();
            let old = b.add_free_ptr(extra[0], int.clone()).unwrap();
            let [old] = b
                .build_unwrap_sum(1, option_type([int.clone()]), old)
                .unwrap();
            let outer = b.add_free_ptr(outer, inner.clone()).unwrap();
            let [current] = b.build_unwrap_sum(1, option_type([inner]), outer).unwrap();
            let current = b.add_free_ptr(current, int.clone()).unwrap();
            let [current] = b.build_unwrap_sum(1, option_type([int]), current).unwrap();
            let sum = b.add_iadd(6, old, current).unwrap();
            b.finish_hugr_with_outputs([sum]).unwrap()
        });
    assert_eq!(exec_ctx.exec_hugr_u64(hugr, "main"), 30);
}

#[rstest]
fn custom_mutex_makes_concurrent_map_exclusive(mut exec_ctx: TestContext) {
    use std::{cell::UnsafeCell, sync::atomic::AtomicU8};
    configure(&mut exec_ctx);
    exec_ctx.add_extensions(|b| b.add_ptr_extensions(SpinCodegen));
    let ty = int_type(6);
    let ptr_ty = ptr::ptr_type(ty.clone());
    let hugr = SimpleHugrConfig::new()
        .with_extensions(STD_REG.to_owned())
        .with_ins([ptr_ty.clone()])
        .with_outs([ptr_ty])
        .finish(|mut b| {
            let mut mb = b.module_root_builder();
            let mut callback = mb
                .define_function("increment", Signature::new_endo([ty.clone()]))
                .unwrap();
            let [value] = callback.input_wires_arr();
            let one = callback.add_load_value(ConstInt::new_u(6, 1).unwrap());
            let value = callback.add_iadd(6, value, one).unwrap();
            let callback = callback.finish_with_outputs([value]).unwrap();
            let function = b.load_func(callback.handle(), &[]).unwrap();
            let [ptr] = b.input_wires_arr();
            let (ptr, _) = b.add_map_ptr(ptr, function, ty, [], []).unwrap();
            b.finish_hugr_with_outputs([ptr]).unwrap()
        });
    let emission = emit(&exec_ctx, &hugr);
    let function = emission.module().get_function("main").unwrap();
    function.set_linkage(inkwell::module::Linkage::External);
    let engine = emission
        .module()
        .create_jit_execution_engine(inkwell::OptimizationLevel::Aggressive)
        .unwrap();
    let address = engine.get_function_address("main").unwrap();
    // Mirror the test spin-mutex cell layout. Each worker owns one of four handles;
    // storage is owned by this test and stays alive until every worker joins.
    #[repr(C)]
    struct Cell {
        mutex: AtomicU8,
        count: u64,
        value: UnsafeCell<u64>,
    }
    let cell = Cell {
        count: 4,
        mutex: AtomicU8::new(0),
        value: UnsafeCell::new(0),
    };
    let ptr = (&cell as *const Cell) as usize;
    std::thread::scope(|scope| {
        for _ in 0..4 {
            scope.spawn(move || {
                // The emitted function takes and returns an opaque cell pointer.
                // Its mutex protects the only accesses to value while threads run.
                let map: unsafe extern "C" fn(usize) -> usize =
                    unsafe { std::mem::transmute(address) };
                for _ in 0..2000 {
                    assert_eq!(unsafe { map(ptr) }, ptr);
                }
            });
        }
    });
    // All workers have joined, so no concurrent access to the value remains.
    assert_eq!(unsafe { *cell.value.get() }, 8000);
    assert_eq!(cell.count, 4);
}

#[derive(Clone)]
struct HookCodegen;

fn hook_void<H: HugrView<Node = Node>>(
    ctx: &mut EmitFuncContext<H>,
    name: &str,
    ptr: PointerValue,
) -> Result<()> {
    let function = ctx.get_extern_func(
        name,
        ctx.iw_context()
            .void_type()
            .fn_type(&[ctx.llvm_ptr_type().into()], false),
    )?;
    ctx.builder().build_call(function, &[ptr.into()], "")?;
    Ok(())
}

impl PtrCodegen for HookCodegen {
    fn emit_alloc<'c, H: HugrView<Node = Node>>(
        &self,
        ctx: &mut EmitFuncContext<'c, '_, H>,
        layout: StructType<'c>,
    ) -> Result<PointerValue<'c>> {
        let i64_t = ctx.iw_context().i64_type();
        let function = ctx.get_extern_func(
            "test_ptr_alloc",
            ctx.llvm_ptr_type()
                .fn_type(&[i64_t.into(), i64_t.into()], false),
        )?;
        Ok(ctx
            .builder()
            .build_call(
                function,
                &[
                    layout.size_of().unwrap().into(),
                    layout.get_alignment().into(),
                ],
                "",
            )?
            .try_as_basic_value()
            .unwrap_basic()
            .into_pointer_value())
    }
    fn emit_free<'c, H: HugrView<Node = Node>>(
        &self,
        ctx: &mut EmitFuncContext<'c, '_, H>,
        ptr: PointerValue<'c>,
    ) -> Result<()> {
        hook_void(ctx, "test_ptr_free", ptr)
    }
    fn emit_get_ptr<'c, H: HugrView<Node = Node>>(
        &self,
        ctx: &mut EmitFuncContext<'c, '_, H>,
        ptr: PointerValue<'c>,
        _layout: StructType<'c>,
    ) -> Result<PointerValue<'c>> {
        let function = ctx.get_extern_func(
            "test_ptr_get_ptr",
            ctx.llvm_ptr_type()
                .fn_type(&[ctx.llvm_ptr_type().into()], false),
        )?;
        Ok(ctx
            .builder()
            .build_call(function, &[ptr.into()], "")?
            .try_as_basic_value()
            .unwrap_basic()
            .into_pointer_value())
    }
    fn emit_lock<'c, H: HugrView<Node = Node>>(
        &self,
        ctx: &mut EmitFuncContext<'c, '_, H>,
        ptr: PointerValue<'c>,
    ) -> Result<()> {
        hook_void(ctx, "test_ptr_lock", ptr)
    }
    fn emit_unlock<'c, H: HugrView<Node = Node>>(
        &self,
        ctx: &mut EmitFuncContext<'c, '_, H>,
        ptr: PointerValue<'c>,
    ) -> Result<()> {
        hook_void(ctx, "test_ptr_unlock", ptr)
    }
}

thread_local! {
    static EVENTS: std::cell::RefCell<Vec<&'static str>> = const { std::cell::RefCell::new(Vec::new()) };
    static ALLOCATIONS: std::cell::RefCell<std::collections::BTreeMap<usize, (std::alloc::Layout, usize)>> = const { std::cell::RefCell::new(std::collections::BTreeMap::new()) };
}
fn event(name: &'static str) {
    EVENTS.with_borrow_mut(|events| events.push(name));
}
extern "C" fn hook_alloc(size: u64, align: u64) -> *mut u8 {
    let payload = std::alloc::Layout::from_size_align(size as usize, align as usize).unwrap();
    let (layout, offset) = std::alloc::Layout::new::<u64>().extend(payload).unwrap();
    // LLVM supplies a nonzero sized cell and its power-of-two ABI alignment.
    let ptr = unsafe { std::alloc::alloc(layout) };
    assert!(!ptr.is_null());
    ALLOCATIONS.with_borrow_mut(|allocs| allocs.insert(ptr as usize, (layout, offset)));
    event("alloc");
    hook_init(ptr.cast());
    ptr
}
extern "C" fn hook_free(ptr: *mut u8) {
    hook_destroy(ptr.cast());
    let (layout, _) = ALLOCATIONS
        .with_borrow_mut(|allocs| allocs.remove(&(ptr as usize)))
        .unwrap();
    // The last Free returns the value and destroys the mutex before freeing.
    unsafe {
        std::alloc::dealloc(ptr, layout);
    }
    event("free");
}
extern "C" fn hook_get_ptr(ptr: *mut u8) -> *mut u8 {
    let offset = ALLOCATIONS.with_borrow(|allocs| allocs[&(ptr as usize)].1);
    // Payload storage is a separate, aligned region after the runtime mutex.
    assert!(offset > 0);
    event("get_ptr");
    unsafe { ptr.add(offset) }
}
extern "C" fn hook_init(ptr: *mut u64) {
    unsafe {
        ptr.write(0);
    }
    event("init");
}
extern "C" fn hook_lock(ptr: *mut u64) {
    assert_eq!(unsafe { ptr.replace(1) }, 0);
    event("lock");
}
extern "C" fn hook_unlock(ptr: *mut u64) {
    assert_eq!(unsafe { ptr.replace(0) }, 1);
    event("unlock");
}
extern "C" fn hook_destroy(ptr: *mut u64) {
    assert_eq!(unsafe { ptr.read() }, 0);
    event("destroy");
}

#[rstest]
fn custom_hooks_manage_cell_once(mut exec_ctx: TestContext) {
    configure(&mut exec_ctx);
    exec_ctx.add_extensions(|b| b.add_ptr_extensions(HookCodegen));
    let hugr = lifecycle();
    let emission = emit(&exec_ctx, &hugr);
    emission
        .module()
        .get_function("main")
        .unwrap()
        .set_linkage(inkwell::module::Linkage::External);
    let engine = emission
        .module()
        .create_jit_execution_engine(inkwell::OptimizationLevel::None)
        .unwrap();
    for (name, address) in [
        ("test_ptr_alloc", hook_alloc as *const () as usize),
        ("test_ptr_free", hook_free as *const () as usize),
        ("test_ptr_get_ptr", hook_get_ptr as *const () as usize),
        ("test_ptr_lock", hook_lock as *const () as usize),
        ("test_ptr_unlock", hook_unlock as *const () as usize),
    ] {
        engine.add_global_mapping(&emission.module().get_function(name).unwrap(), address);
    }
    EVENTS.with_borrow_mut(Vec::clear);
    // This test's entry has no arguments and returns the LLVM boolean type.
    let main = unsafe {
        engine
            .get_function::<unsafe extern "C" fn() -> bool>("main")
            .unwrap()
    };
    assert!(unsafe { main.call() });
    EVENTS.with_borrow(|events| {
        assert_eq!(
            events,
            &[
                "alloc", "init", "get_ptr", "lock", "get_ptr", "unlock", "lock", "get_ptr",
                "unlock", "lock", "get_ptr", "unlock", "lock", "get_ptr", "unlock", "lock",
                "get_ptr", "unlock", "lock", "get_ptr", "unlock", "destroy", "free",
            ]
        )
    });
    ALLOCATIONS.with_borrow(|allocs| assert!(allocs.is_empty()));
}

#[derive(Clone)]
struct SpinCodegen;
impl PtrCodegen for SpinCodegen {
    fn emit_alloc<'c, H: HugrView<Node = Node>>(
        &self,
        ctx: &mut EmitFuncContext<'c, '_, H>,
        layout: StructType<'c>,
    ) -> Result<PointerValue<'c>> {
        let storage = ctx
            .iw_context()
            .struct_type(&[ctx.iw_context().i8_type().into(), layout.into()], false);
        let ptr = DefaultPtrCodegen.emit_alloc(ctx, storage)?;
        ctx.builder()
            .build_store(ptr, ctx.iw_context().i8_type().const_zero())?;
        Ok(ptr)
    }
    fn emit_get_ptr<'c, H: HugrView<Node = Node>>(
        &self,
        ctx: &mut EmitFuncContext<'c, '_, H>,
        ptr: PointerValue<'c>,
        layout: StructType<'c>,
    ) -> Result<PointerValue<'c>> {
        let storage = ctx
            .iw_context()
            .struct_type(&[ctx.iw_context().i8_type().into(), layout.into()], false);
        Ok(ctx
            .builder()
            .build_struct_gep(storage, ptr, 1, "test.payload")?)
    }
    fn emit_lock<'c, H: HugrView<Node = Node>>(
        &self,
        ctx: &mut EmitFuncContext<'c, '_, H>,
        mutex: PointerValue<'c>,
    ) -> Result<()> {
        let spin = ctx.new_basic_block("test.lock", None);
        let acquired = ctx.new_basic_block("test.locked", None);
        ctx.builder().build_unconditional_branch(spin)?;
        ctx.builder().position_at_end(spin);
        let byte = ctx.iw_context().i8_type();
        let old = ctx.builder().build_atomicrmw(
            inkwell::AtomicRMWBinOp::Xchg,
            mutex,
            byte.const_int(1, false),
            inkwell::AtomicOrdering::Acquire,
        )?;
        let available =
            ctx.builder()
                .build_int_compare(IntPredicate::EQ, old, byte.const_zero(), "")?;
        ctx.builder()
            .build_conditional_branch(available, acquired, spin)?;
        ctx.builder().position_at_end(acquired);
        Ok(())
    }
    fn emit_unlock<'c, H: HugrView<Node = Node>>(
        &self,
        ctx: &mut EmitFuncContext<'c, '_, H>,
        mutex: PointerValue<'c>,
    ) -> Result<()> {
        ctx.builder()
            .build_store(mutex, ctx.iw_context().i8_type().const_zero())?
            .set_atomic_ordering(inkwell::AtomicOrdering::Release)
            .unwrap();
        Ok(())
    }
}

#[rstest]
fn default_mutex_emits_no_synchronization(mut exec_ctx: TestContext) {
    configure(&mut exec_ctx);
    let hugr = lifecycle();
    let emission = emit(&exec_ctx, &hugr);
    let ir = emission.module().print_to_string().to_string();
    assert!(ir.contains("@malloc("));
    assert!(ir.contains("@free("));
    assert!(!ir.contains("atomic"));
    assert!(!ir.contains("@aligned_alloc("));
}
