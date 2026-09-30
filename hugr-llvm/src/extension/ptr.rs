//! Lowering for shared pointer cells.
//!
//! Register [`PtrCodegenExtension`] with a [`PtrCodegen`] implementation to
//! customize allocation and mutex handling. [`DefaultPtrCodegen`] uses the
//! existing libc `malloc`/`free` helpers and no-op mutex hooks. Targets that
//! execute shared handles concurrently must supply synchronization hooks.
//!
//! Each cell contains a reference count, optional mutex storage, and the stored
//! value. Every operation except creation calls the lock and unlock hooks.
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
    std_extensions::ptr::{self, PtrOp, PtrOpDef},
    types::Signature,
};
use inkwell::{
    IntPredicate,
    types::{BasicTypeEnum, StructType},
    values::{BasicValueEnum, IntValue, PointerValue},
};

use crate::{
    CodegenExtension, CodegenExtsBuilder,
    emit::{
        EmitFuncContext, RowPromise, deaggregate_call_result,
        libc::{emit_libc_abort, emit_libc_free, emit_libc_malloc},
    },
    types::TypingSession,
};

/// Runtime hooks for pointer cells.
///
/// Allocation and deallocation must be paired. The default mutex hooks do
/// nothing and require that accesses to a cell do not run concurrently. For
/// concurrent use, provide mutual exclusion and acquire/release synchronization
/// between all handles to a cell.
/// Override the mutex type, initialization, and destruction as well as lock and
/// unlock when using a target-specific mutex representation. Hooks must leave
/// the builder at the end of an unterminated basic block.
pub trait PtrCodegen: Clone {
    /// Allocate storage for `layout`, aligned for every field, or terminate.
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

    /// Deallocate a cell after its last handle is released and its mutex destroyed.
    /// The default emits libc `free` and must be paired with [`Self::emit_alloc`].
    fn emit_free<'c, H: HugrView<Node = Node>>(
        &self,
        ctx: &mut EmitFuncContext<'c, '_, H>,
        ptr: PointerValue<'c>,
    ) -> Result<()> {
        emit_libc_free(ctx, ptr.into())
    }

    /// Storage type for the embedded mutex. The default is an empty struct.
    fn mutex_type<'c>(&self, ts: &TypingSession<'c, '_>) -> BasicTypeEnum<'c> {
        ts.iw_context().struct_type(&[], false).into()
    }

    /// Initialize an unlocked mutex before publishing the cell. Defaults to no-op.
    /// The pointer addresses the mutex field, not the entire cell.
    fn emit_init_mutex<'c, H: HugrView<Node = Node>>(
        &self,
        _ctx: &mut EmitFuncContext<'c, '_, H>,
        _mutex: PointerValue<'c>,
    ) -> Result<()> {
        Ok(())
    }

    /// Acquire exclusive access through the mutex field pointer. Defaults to no-op.
    fn emit_lock<'c, H: HugrView<Node = Node>>(
        &self,
        _ctx: &mut EmitFuncContext<'c, '_, H>,
        _mutex: PointerValue<'c>,
    ) -> Result<()> {
        Ok(())
    }

    /// Release exclusive access and publish writes. Defaults to no-op.
    fn emit_unlock<'c, H: HugrView<Node = Node>>(
        &self,
        _ctx: &mut EmitFuncContext<'c, '_, H>,
        _mutex: PointerValue<'c>,
    ) -> Result<()> {
        Ok(())
    }

    /// Destroy an unlocked mutex after the final release. Defaults to no-op.
    fn emit_destroy_mutex<'c, H: HugrView<Node = Node>>(
        &self,
        _ctx: &mut EmitFuncContext<'c, '_, H>,
        _mutex: PointerValue<'c>,
    ) -> Result<()> {
        Ok(())
    }
}

/// Pointer lowering with libc allocation and no-op mutex hooks.
#[derive(Clone, Debug, Default)]
pub struct DefaultPtrCodegen;
impl PtrCodegen for DefaultPtrCodegen {}

/// Registers the pointer type and all seven pointer operations.
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
    let value_ty = ctx.llvm_type(&op.ty)?;
    let count_ty = ctx.iw_context().i64_type();
    let cell_ty = ctx.iw_context().struct_type(
        &[
            count_ty.into(),
            ccg.mutex_type(&ctx.typing_session()),
            value_ty,
        ],
        false,
    );
    let cell = if op.def == PtrOpDef::New {
        ccg.emit_alloc(ctx, cell_ty)?
    } else {
        inputs[0].into_pointer_value()
    };
    let count_ptr = ctx
        .builder()
        .build_struct_gep(cell_ty, cell, 0, "ptr.count")?;
    let mutex = ctx
        .builder()
        .build_struct_gep(cell_ty, cell, 1, "ptr.mutex")?;
    let value_ptr = ctx
        .builder()
        .build_struct_gep(cell_ty, cell, 2, "ptr.value")?;
    if op.def == PtrOpDef::New {
        ctx.builder()
            .build_store(count_ptr, count_ty.const_int(1, false))?;
        ccg.emit_init_mutex(ctx, mutex)?;
        ctx.builder().build_store(value_ptr, inputs[0])?;
        return outputs.finish(ctx.builder(), [cell.into()]);
    }
    ccg.emit_lock(ctx, mutex)?;
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
            ccg.emit_unlock(ctx, mutex)?;
            ccg.emit_destroy_mutex(ctx, mutex)?;
            ccg.emit_free(ctx, cell)?;
            ctx.builder().build_unconditional_branch(exit)?;
            ctx.builder().position_at_end(shared_bb);
            let none = sum_ty.build_tag(ctx.builder(), 0, vec![])?;
            mailbox.write(ctx.builder(), [none.into()])?;
            ccg.emit_unlock(ctx, mutex)?;
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
    ccg.emit_unlock(ctx, mutex)?;
    outputs.finish(ctx.builder(), results)
}

#[cfg(test)]
mod test;
