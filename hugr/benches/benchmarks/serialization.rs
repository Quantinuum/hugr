//! Serialization benchmarks for a representative Guppy-generated HUGR.

use crate::examples::{big_hugr, simple_cfg_hugr, t_factory};
use criterion::{Criterion, criterion_group};
use hugr::Hugr;
use hugr::HugrView;
use hugr::envelope::{EnvelopeConfig, EnvelopeFormat};
use hugr::extension::ExtensionRegistry;
use std::hint::black_box;

/// An envelope format and its explicit uncompressed encoding configuration.
struct Serializer {
    name: &'static str,
    config: EnvelopeConfig,
    include_extensions: bool,
}

/// Returns every serialization format covered by these benchmarks.
///
/// Compression is explicitly disabled so the timings only cover serialization.
///
/// Each format is measured with and without embedding extension definitions.
fn serializers() -> [Serializer; 4] {
    [
        Serializer {
            name: "capnp/without_extensions",
            config: EnvelopeConfig::new(EnvelopeFormat::Model),
            include_extensions: false,
        },
        Serializer {
            name: "capnp/with_extensions",
            config: EnvelopeConfig::new(EnvelopeFormat::ModelWithExtensions),
            include_extensions: true,
        },
        Serializer {
            name: "sexpr/without_extensions",
            config: EnvelopeConfig::new(EnvelopeFormat::SExpression),
            include_extensions: false,
        },
        Serializer {
            name: "sexpr/with_extensions",
            config: EnvelopeConfig::new(EnvelopeFormat::SExpressionWithExtensions),
            include_extensions: true,
        },
    ]
}

/// Encodes a HUGR with the supplied envelope configuration.
fn encode(hugr: &Hugr, serializer: &Serializer) -> Vec<u8> {
    // Always disable compression, since we are not benchmarking zstd here.
    let config = serializer.config.disable_compression();

    let mut bytes = Vec::new();
    if serializer.include_extensions {
        hugr.store_with_exts(&mut bytes, config, hugr.extensions())
    } else {
        hugr.store(&mut bytes, config)
    }
    .expect("benchmark HUGRs should always be serializable");
    bytes
}

/// Decodes an envelope using its packaged extensions when available.
fn decode(bytes: &[u8], registry: &ExtensionRegistry, serializer: &Serializer) -> Hugr {
    let extensions = (!serializer.include_extensions).then_some(registry);
    Hugr::load(bytes, extensions).expect("benchmark envelopes should always be decodable")
}

/// Benchmarks uncompressed encoding and decoding of a hugr.
fn bench_hugr(c: &mut Criterion, name: &str, hugr: &Hugr) {
    for serializer in serializers() {
        c.bench_function(
            &format!("serialization/{name}/{}/encode", serializer.name),
            |b| {
                b.iter(|| black_box(encode(hugr, &serializer)));
            },
        );

        let bytes = encode(hugr, &serializer);
        c.bench_function(
            &format!("serialization/{name}/{}/decode", serializer.name),
            |b| {
                b.iter(|| black_box(decode(black_box(&bytes), hugr.extensions(), &serializer)));
            },
        );
    }
}

/// Benchmarks every representative HUGR used by the serialization suite.
fn bench_serialization(c: &mut Criterion) {
    bench_hugr(c, "t_factory", &t_factory());
    bench_hugr(c, "simple_cfg", &simple_cfg_hugr());

    for byte_size in [1024, 1024 * 1024] {
        bench_hugr(c, &format!("big_hugr/{byte_size}"), &big_hugr(byte_size));
    }
}

criterion_group! {
    name = benches;
    config = Criterion::default();
    targets = bench_serialization
}
