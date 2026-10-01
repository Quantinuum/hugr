//! Lowering for shared pointer cells.
//!
//! Register [`PtrCodegenExtension`] with a [`PtrCodegen`] implementation to
//! customize allocation and mutex handling. [`DefaultPtrCodegen`] uses the
//! existing libc `malloc`/`free` helpers and no-op mutex hooks. Targets that
//! execute shared handles concurrently must supply synchronization hooks.
//!
//! Allocation returns an opaque runtime handle. Its payload contains the reference
//! count and stored value; the runtime owns any mutex and its lifecycle. Every
//! operation except creation and identity comparison calls the lock and unlock
//! hooks on the handle. `Eq` compares opaque handles without accessing the payload.
//! `Map` holds the lock throughout its callback. Callbacks must not access the
//! same cell through another handle: this can deadlock a non-reentrant mutex
//! or access a linear value already owned by the callback. A callback that does
//! not return normally does not unlock the cell.
//!
//! Threaded pointer values order operations. Operations on duplicated handles
//! have unspecified relative order even when a target mutex serializes them.

use anyhow::{Result, anyhow, bail};
use hugr_core::{
    HugrView, Node,
    extension::{prelude::option_type, simple_op::MakeExtensionOp},
    ops::Value,
    std_extensions::ptr::{self, PtrOp, PtrOpDef},
    types::Signature,
};
use inkwell::{
    IntPredicate,
    types::StructType,
    values::{BasicValueEnum, IntValue, PointerValue},
};

use crate::{
    CodegenExtension, CodegenExtsBuilder,
    emit::{
        EmitFuncContext, RowPromise, deaggregate_call_result, emit_value,
        libc::{emit_libc_abort, emit_libc_free, emit_libc_malloc},
    },
};

/// Runtime hooks for pointer cells.
///
/// Allocation and deallocation must be paired. The default mutex hooks do
/// nothing and require that accesses to a cell do not run concurrently. For
/// concurrent use, provide mutual exclusion and acquire/release synchronization
/// between all handles to a cell.
/// Allocation returns an opaque handle with any mutex already initialized. Handles
/// to the same live cell must have the same address, and distinct live cells must
/// have distinct addresses: identity comparison uses the handle directly. Free
/// owns mutex teardown. Lock, unlock, and payload projection receive that same
/// handle, so the lowering does not depend on the runtime storage layout. Hooks
/// must leave the builder at the end of an unterminated basic block.
pub trait PtrCodegen: Clone {
    /// Allocate an opaque handle with space for `layout` and initialize any mutex.
    /// The payload must be aligned for every field; allocation failure must terminate.
    /// `layout` contains the lowering-owned reference count and stored HUGR value.
    /// The default uses [`emit_libc_malloc`] with the LLVM cell size and aborts
    /// on allocation failure. Override it for types requiring alignment beyond
    /// what the target's libc `malloc` provides.
    fn emit_alloc<'c, H: HugrView<Node = Node>>(
        &self,
        ctx: &mut EmitFuncContext<'c, '_, H>,
        layout: StructType<'c>,
    ) -> Result<PointerValue<'c>> {
        let size = layout
            .size_of()
            .ok_or_else(|| anyhow!("Unsized pointer cell"))?;
        let ptr = emit_libc_malloc(ctx, size.into())?.into_pointer_value();
        let failed = ctx.builder().build_is_null(ptr, "ptr.alloc.failed")?;
        abort_if(ctx, failed)?;
        Ok(ptr)
    }

    /// Destroy any mutex and deallocate the opaque handle after its final release.
    /// The handle is unlocked and its stored value has already been recovered.
    /// The default emits libc `free` and must be paired with [`Self::emit_alloc`].
    fn emit_free<'c, H: HugrView<Node = Node>>(
        &self,
        ctx: &mut EmitFuncContext<'c, '_, H>,
        ptr: PointerValue<'c>,
    ) -> Result<()> {
        emit_libc_free(ctx, ptr.into())
    }

    /// Project the payload from an opaque handle returned by [`Self::emit_alloc`].
    /// The result must point to live, aligned storage for the supplied `layout`
    /// (reference count followed by the HUGR value). The lowering initializes it.
    /// Called under the lock, or during creation before the handle is published.
    /// The default allocation is the payload itself, so this returns `ptr`.
    fn emit_get_ptr<'c, H: HugrView<Node = Node>>(
        &self,
        _ctx: &mut EmitFuncContext<'c, '_, H>,
        ptr: PointerValue<'c>,
        _layout: StructType<'c>,
    ) -> Result<PointerValue<'c>> {
        Ok(ptr)
    }

    /// Acquire exclusive access through the opaque handle. Defaults to no-op.
    fn emit_lock<'c, H: HugrView<Node = Node>>(
        &self,
        _ctx: &mut EmitFuncContext<'c, '_, H>,
        _ptr: PointerValue<'c>,
    ) -> Result<()> {
        Ok(())
    }

    /// Release exclusive access and publish writes. Defaults to no-op.
    fn emit_unlock<'c, H: HugrView<Node = Node>>(
        &self,
        _ctx: &mut EmitFuncContext<'c, '_, H>,
        _ptr: PointerValue<'c>,
    ) -> Result<()> {
        Ok(())
    }
}

/// Pointer lowering with libc allocation and no-op mutex hooks.
#[derive(Clone, Debug, Default)]
pub struct DefaultPtrCodegen;
impl PtrCodegen for DefaultPtrCodegen {}

/// Registers the pointer type and all pointer operations.
#[derive(Clone, Debug, Default)]
pub struct PtrCodegenExtension<CCG>(CCG);
impl<CCG: PtrCodegen> PtrCodegenExtension<CCG> {
    /// Use the supplied runtime hooks.
    pub fn new(ccg: CCG) -> Self {
        Self(ccg)
    }
}
impl<CCG: PtrCodegen> From<CCG> for PtrCodegenExtension<CCG> {
    fn from(ccg: CCG) -> Self {
        Self::new(ccg)
    }
}
impl<'a, H: HugrView<Node = Node> + 'a> CodegenExtsBuilder<'a, H> {
    /// Register pointer lowering using the supplied runtime hooks.
    pub fn add_ptr_extensions(self, ccg: impl PtrCodegen + 'a) -> Self {
        self.add_extension(PtrCodegenExtension::new(ccg))
    }
    /// Register pointer lowering with [`DefaultPtrCodegen`].
    pub fn add_default_ptr_extensions(self) -> Self {
        self.add_ptr_extensions(DefaultPtrCodegen)
    }
}
impl<CCG: PtrCodegen> CodegenExtension for PtrCodegenExtension<CCG> {
    fn add_extension<'a, H: HugrView<Node = Node> + 'a>(
        self,
        builder: CodegenExtsBuilder<'a, H>,
    ) -> CodegenExtsBuilder<'a, H>
    where
        Self: 'a,
    {
        builder
            .custom_type((ptr::EXTENSION_ID, ptr::PTR_TYPE_ID), |ts, _| {
                Ok(ts.llvm_ptr_type().into())
            })
            .simple_extension_op::<PtrOpDef>(move |ctx, args, _| {
                let op = PtrOp::from_extension_op(args.node().as_ref())?;
                emit_ptr_op(&self.0, ctx, op, args.inputs, args.outputs)
            })
    }
}

fn abort_if<H: HugrView<Node = Node>>(ctx: &mut EmitFuncContext<H>, cond: IntValue) -> Result<()> {
    let failed = ctx.new_basic_block("ptr.abort", None);
    let success = ctx.new_basic_block("ptr.continue", None);
    ctx.builder()
        .build_conditional_branch(cond, failed, success)?;
    ctx.builder().position_at_end(failed);
    emit_libc_abort(ctx)?;
    ctx.builder().build_unreachable()?;
    ctx.builder().position_at_end(success);
    Ok(())
}

fn emit_ptr_op<'c, H: HugrView<Node = Node>>(
    ccg: &impl PtrCodegen,
    ctx: &mut EmitFuncContext<'c, '_, H>,
    op: PtrOp,
    inputs: Vec<BasicValueEnum<'c>>,
    outputs: RowPromise<'c>,
) -> Result<()> {
    if op.def == PtrOpDef::Eq {
        let equal = ctx.builder().build_int_compare(
            IntPredicate::EQ,
            inputs[0].into_pointer_value(),
            inputs[1].into_pointer_value(),
            "ptr.eq",
        )?;
        let true_val = emit_value(ctx, &Value::true_val())?;
        let false_val = emit_value(ctx, &Value::false_val())?;
        let equal = ctx.builder().build_select(equal, true_val, false_val, "")?;
        return outputs.finish(ctx.builder(), [inputs[0], inputs[1], equal]);
    }
    let value_ty = ctx.llvm_type(&op.ty)?;
    let count_ty = ctx.iw_context().i64_type();
    let cell_ty = ctx
        .iw_context()
        .struct_type(&[count_ty.into(), value_ty], false);
    let cell = if op.def == PtrOpDef::New {
        ccg.emit_alloc(ctx, cell_ty)?
    } else {
        inputs[0].into_pointer_value()
    };
    if op.def != PtrOpDef::New {
        ccg.emit_lock(ctx, cell)?;
    }
    let payload = ccg.emit_get_ptr(ctx, cell, cell_ty)?;
    let count_ptr = ctx
        .builder()
        .build_struct_gep(cell_ty, payload, 0, "ptr.count")?;
    let value_ptr = ctx
        .builder()
        .build_struct_gep(cell_ty, payload, 1, "ptr.value")?;
    if op.def == PtrOpDef::New {
        ctx.builder()
            .build_store(count_ptr, count_ty.const_int(1, false))?;
        ctx.builder().build_store(value_ptr, inputs[0])?;
        return outputs.finish(ctx.builder(), [cell.into()]);
    }
    let results = match op.def {
        PtrOpDef::Read => vec![
            cell.into(),
            ctx.builder().build_load(value_ty, value_ptr, "ptr.read")?,
        ],
        PtrOpDef::Write => {
            ctx.builder().build_store(value_ptr, inputs[1])?;
            vec![cell.into()]
        }
        PtrOpDef::Swap => {
            let old = ctx.builder().build_load(value_ty, value_ptr, "ptr.old")?;
            ctx.builder().build_store(value_ptr, inputs[1])?;
            vec![cell.into(), old]
        }
        PtrOpDef::Dup => {
            let count = ctx
                .builder()
                .build_load(count_ty, count_ptr, "")?
                .into_int_value();
            let overflow = ctx.builder().build_int_compare(
                IntPredicate::EQ,
                count,
                count_ty.const_all_ones(),
                "ptr.refcount.overflow",
            )?;
            abort_if(ctx, overflow)?;
            let count = ctx
                .builder()
                .build_int_add(count, count_ty.const_int(1, false), "")?;
            ctx.builder().build_store(count_ptr, count)?;
            vec![cell.into(), cell.into()]
        }
        PtrOpDef::Free => {
            let count = ctx
                .builder()
                .build_load(count_ty, count_ptr, "")?
                .into_int_value();
            let count = ctx
                .builder()
                .build_int_sub(count, count_ty.const_int(1, false), "")?;
            ctx.builder().build_store(count_ptr, count)?;
            let last = ctx.builder().build_int_compare(
                IntPredicate::EQ,
                count,
                count_ty.const_zero(),
                "ptr.last",
            )?;
            let last_bb = ctx.new_basic_block("ptr.free.last", None);
            let shared_bb = ctx.new_basic_block("ptr.free.shared", None);
            let exit = ctx.new_basic_block("ptr.free.exit", None);
            let option = option_type([op.ty]);
            let sum_ty = ctx.llvm_sum_type(option.clone())?;
            let mailbox = ctx.new_row_mail_box([&option.into()], "ptr.free.result")?;
            ctx.builder()
                .build_conditional_branch(last, last_bb, shared_bb)?;
            ctx.builder().position_at_end(last_bb);
            let value = ctx.builder().build_load(value_ty, value_ptr, "ptr.take")?;
            let some = sum_ty.build_tag(ctx.builder(), 1, vec![value])?;
            mailbox.write(ctx.builder(), [some.into()])?;
            ccg.emit_unlock(ctx, cell)?;
            ccg.emit_free(ctx, cell)?;
            ctx.builder().build_unconditional_branch(exit)?;
            ctx.builder().position_at_end(shared_bb);
            let none = sum_ty.build_tag(ctx.builder(), 0, vec![])?;
            mailbox.write(ctx.builder(), [none.into()])?;
            ccg.emit_unlock(ctx, cell)?;
            ctx.builder().build_unconditional_branch(exit)?;
            ctx.builder().position_at_end(exit);
            return outputs.finish(ctx.builder(), mailbox.read_vec(ctx.builder(), [])?);
        }
        PtrOpDef::Map => {
            let mut in_row = vec![op.ty.clone()];
            in_row.extend(op.map_signature.input().iter().cloned());
            let mut out_row = vec![op.ty];
            out_row.extend(op.map_signature.output().iter().cloned());
            let callback_ty = ctx.llvm_func_type(&Signature::new(in_row, out_row))?;
            let value = ctx
                .builder()
                .build_load(value_ty, value_ptr, "ptr.map.input")?;
            let mut args = vec![value.into()];
            args.extend(
                inputs[2..]
                    .iter()
                    .copied()
                    .map(inkwell::values::BasicMetadataValueEnum::from),
            );
            let call = ctx.builder().build_indirect_call(
                callback_ty,
                inputs[1].into_pointer_value(),
                &args,
                "ptr.map",
            )?;
            let mut values =
                deaggregate_call_result(ctx.builder(), call, 1 + op.map_signature.output().len())?;
            ctx.builder().build_store(value_ptr, values[0])?;
            values[0] = cell.into();
            values
        }
        _ => bail!("Unsupported pointer operation: {:?}", op.def),
    };
    ccg.emit_unlock(ctx, cell)?;
    outputs.finish(ctx.builder(), results)
}

#[cfg(test)]
mod test;
