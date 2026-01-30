use ascent::rayon::vec;
use hugr_core::Hugr;
use hugr_core::builder::{
    BuildError, BuildHandle, HugrBuilder, ModuleBuilder, dataflow::FunctionBuilder,
};
use hugr_core::ops::handle::FuncID;

pub(crate) mod test_quantum_extension {


    use std::sync::{Arc, LazyLock};

    use hugr_core::ops::{OpName, OpNameRef};
    use hugr_core::types::FuncValueType;
    use hugr_core::{
        Extension,
        extension::{
            ExtensionId,
            prelude::{bool_t, qb_t},
        },
        ops::ExtensionOp,
        std_extensions::arithmetic::float_types,
        type_row,
        types::{PolyFuncTypeRV, Signature},
    };

    fn one_qb_func() -> PolyFuncTypeRV {
        FuncValueType::new_endo(qb_t()).into()
    }

    fn two_qb_func() -> PolyFuncTypeRV {
        FuncValueType::new_endo(vec![qb_t(), qb_t()]).into()
    }
    /// The extension identifier.
    pub const EXTENSION_ID: ExtensionId = ExtensionId::new_unchecked("test.quantum");
    fn extension() -> Arc<Extension> {
        Extension::new_test_arc(EXTENSION_ID, |extension, extension_ref| {
            extension
                .add_op(
                    OpName::new_inline("H"),
                    "Hadamard".into(),
                    one_qb_func(),
                    extension_ref,
                )
                .unwrap();
            // extension
            //     .add_op(
            //         OpName::new_inline("RzF64"),
            //         "Rotation specified by float".into(),
            //         Signature::new(vec![qb_t(), float_types::float64_type()], vec![qb_t()]),
            //         extension_ref,
            //     )
            //     .unwrap();

            extension
                .add_op(
                    OpName::new_inline("CX"),
                    "CX".into(),
                    two_qb_func(),
                    extension_ref,
                )
                .unwrap();

            // extension
            //     .add_op(
            //         OpName::new_inline("Measure"),
            //         "Measure a qubit, returning the qubit and the measurement result.".into(),
            //         Signature::new(vec![qb_t()], vec![qb_t(), bool_t()]),
            //         extension_ref,
            //     )
            //     .unwrap();

            // extension
            //     .add_op(
            //         OpName::new_inline("QAlloc"),
            //         "Allocate a new qubit.".into(),
            //         Signature::new(type_row![], vec![qb_t()]),
            //         extension_ref,
            //     )
            //     .unwrap();

            // extension
            //     .add_op(
            //         OpName::new_inline("QDiscard"),
            //         "Discard a qubit.".into(),
            //         Signature::new(vec![qb_t()], type_row![]),
            //         extension_ref,
            //     )
            //     .unwrap();
        })
    }

    /// Quantum extension definition.
    pub static EXTENSION: LazyLock<Arc<Extension>> = LazyLock::new(extension);

    fn get_gate(gate_name: &OpNameRef) -> ExtensionOp {
        EXTENSION.instantiate_extension_op(gate_name, []).unwrap()
    }
    pub(crate) fn h_gate() -> ExtensionOp {
        get_gate("H")
    }

    pub(crate) fn cx_gate() -> ExtensionOp {
        get_gate("CX")
    }

    // pub(crate) fn measure() -> ExtensionOp {
    //     get_gate("Measure")
    // }

    // pub(crate) fn rz_f64() -> ExtensionOp {
    //     get_gate("RzF64")
    // }

    // pub(crate) fn q_alloc() -> ExtensionOp {
    //     get_gate("QAlloc")
    // }

    // pub(crate) fn q_discard() -> ExtensionOp {
    //     get_gate("QDiscard")
    // }
}

pub(crate) fn build_simple_hugr(
    num_qubits: usize,
    f: impl FnOnce(FunctionBuilder<&mut Hugr>) -> Result<BuildHandle<FuncID<true>>, BuildError>,
) -> Result<Hugr, BuildError> {
    use hugr_core::{extension::prelude::qb_t, types::Signature};

    let qb_row = vec![qb_t(); num_qubits];
    let signature = Signature::new(qb_row.clone(), qb_row);

    let mut module_builder = ModuleBuilder::new();
    let f_builder = module_builder.define_function("main", signature)?;

    f(f_builder)?;

    Ok(module_builder.finish_hugr()?)
}



// pub(crate) fn build_simple_circuit<F>(
//     num_qubits: usize,
//     h: impl FnOnce(&mut FunctionBuilder<Hugr>) -> Result<BuildHandle<FuncID<true>>, BuildError>,
// ) -> Result<Hugr, BuildError>
//     // F: FnOnce(
//     //     &mut hugr::builder::CircuitBuilder<'_, hugr::builder::FunctionBuilder<hugr::Hugr>>,
//     // ) -> Result<(), hugr::builder::BuildError>,
// {
//     use hugr_core::{extension::prelude::qb_t, types::Signature};
//     use hugr_core::builder::Dataflow;
//     use hugr_core::builder::DataflowHugr;

//     let mut f = FunctionBuilder::new("name", Signature::new_endo(vec![qb_t(); num_qubits]))?;
//     let [q0, q1] = f.input_wires_arr();



//     h(&mut f)?;


//     let hugr = f.finish_hugr_with_outputs([q0, q1])?;
//     Ok(hugr.into())
// }
