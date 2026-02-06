// Required for black_box uses
#![allow(clippy::unit_arg)]

use std::hint::black_box;

use criterion::{AxisScale, BenchmarkId, Criterion, PlotConfiguration, criterion_group};
use hugr_passes::hash::HugrHash;

use super::hugr::examples::circuit;

fn bench_hash_simple(c: &mut Criterion) {
    let mut g = c.benchmark_group("hash a simple circuit");
    g.plot_config(PlotConfiguration::default().summary_scale(AxisScale::Logarithmic));

    for size in [10, 100, 1_000] {
        g.bench_with_input(BenchmarkId::new("hash_simple", size), &size, |b, size| {
            let (circ, _) = circuit(*size);
            b.iter(|| black_box(circ.hugr_hash()))
        });
    }
    g.finish();
}

criterion_group! {
    name = benches;
    config = Criterion::default();
    targets =
        bench_hash_simple,
}
