//! Double-precision math operations. Angles are in radians.

use std::sync::{Arc, LazyLock, Weak};

use strum::{EnumIter, EnumString, IntoStaticStr};

use super::float_types::float64_type;
use crate::{
    Extension,
    extension::{
        ExtensionId, OpDef, SignatureFunc, Version,
        simple_op::{MakeOpDef, MakeRegisteredOp, OpLoadError, try_from_name},
    },
    ops::OpName,
    types::Signature,
};

/// The math extension identifier.
pub const EXTENSION_ID: ExtensionId = ExtensionId::new_unchecked("arithmetic.math");
/// The math extension version.
pub const VERSION: Version = Version::new(0, 1, 0);

/// Math functions operating on 64-bit floats.
#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq, EnumIter, IntoStaticStr, EnumString)]
#[allow(non_camel_case_types)]
#[non_exhaustive]
pub enum MathOps {
    /// Sine of an angle in radians.
    sin,
    /// Cosine of an angle in radians.
    cos,
    /// Tangent of an angle in radians.
    tan,
    /// Inverse tangent, in radians.
    atan,
    /// Four-quadrant inverse tangent of (y, x), in radians.
    atan2,
    /// Inverse sine, in radians.
    asin,
    /// Inverse cosine, in radians.
    acos,
    /// Natural exponential.
    exp,
    /// Base-two exponential.
    exp2,
    /// Natural logarithm.
    log,
    /// Base-two logarithm.
    log2,
    /// Base-ten logarithm.
    log10,
    /// First input raised to the power of the second input.
    pow,
    /// Remainder of the first input divided by the second, truncating toward zero.
    fmod,
}

impl MathOps {
    fn arity(self) -> (usize, usize) {
        match self {
            Self::pow | Self::fmod | Self::atan2 => (2, 1),
            _ => (1, 1),
        }
    }
}

impl MakeOpDef for MathOps {
    fn opdef_id(&self) -> OpName {
        <&Self as Into<&'static str>>::into(self).into()
    }

    fn from_def(op_def: &OpDef) -> Result<Self, OpLoadError> {
        try_from_name(op_def.name(), op_def.extension_id())
    }

    fn extension(&self) -> ExtensionId {
        EXTENSION_ID
    }

    fn extension_ref(&self) -> Weak<Extension> {
        Arc::downgrade(&EXTENSION)
    }

    fn init_signature(&self, _extension_ref: &Weak<Extension>) -> SignatureFunc {
        let (inputs, outputs) = self.arity();
        Signature::new(vec![float64_type(); inputs], vec![float64_type(); outputs]).into()
    }

    fn description(&self) -> String {
        format!("Double-precision {} math function", self.opdef_id())
    }
}

/// HUGR definitions for the math operations.
pub static EXTENSION: LazyLock<Arc<Extension>> = LazyLock::new(|| {
    Extension::new_arc(EXTENSION_ID, VERSION, |extension, extension_ref| {
        MathOps::load_all_ops(extension, extension_ref).unwrap();
    })
});

impl MakeRegisteredOp for MathOps {
    fn extension_id(&self) -> ExtensionId {
        EXTENSION_ID
    }

    fn extension_ref(&self) -> Arc<Extension> {
        EXTENSION.clone()
    }
}
