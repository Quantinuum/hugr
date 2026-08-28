use crate::examples::{dfg_calling_defn_decl, simple_cfg_hugr, simple_dfg_hugr};
use criterion::{AxisScale, BatchSize, Criterion, PlotConfiguration, criterion_group};
use hugr::HugrView;
use hugr::hugr::hugrmut::HugrMut;
use hugr::ops::handle::NodeHandle;
use std::hint::black_box;

fn bench_builder(c: &mut Criterion) {
    let mut group = c.benchmark_group("builder");
    group.plot_config(PlotConfiguration::default().summary_scale(AxisScale::Logarithmic));
    group.bench_function("simple_dfg", |b| b.iter(|| black_box(simple_dfg_hugr())));
    group.bench_function("simple_cfg", |b| b.iter(|| black_box(simple_cfg_hugr())));
    group.finish();
}

fn bench_insertion(c: &mut Criterion) {
    let mut group = c.benchmark_group("insertion");
    group.plot_config(PlotConfiguration::default().summary_scale(AxisScale::Logarithmic));
    group.bench_function("insert_from_view", |b| {
        let mut h1 = simple_dfg_hugr();
        let h2 = simple_cfg_hugr();
        b.iter(|| black_box(h1.insert_from_view(h1.entrypoint(), &h2)))
    });
    group.bench_function("insert_hugr", |b| {
        b.iter_batched(
            || (simple_dfg_hugr(), simple_cfg_hugr()),
            |(mut h, insert)| black_box(h.insert_hugr(h.entrypoint(), insert)),
            BatchSize::SmallInput,
        )
    });
    group.bench_function("insert_view_forest", |b| {
        let (insert, decl, defn) = dfg_calling_defn_decl();
        b.iter_batched(
            || {
                let h = simple_dfg_hugr();
                let nodes = insert.entry_descendants().chain([defn.node(), decl.node()]);
                let roots = [
                    (insert.entrypoint(), h.entrypoint()),
                    (defn.node(), h.module_root()),
                    (decl.node(), h.module_root()),
                ];
                (h, &insert, nodes, roots)
            },
            |(mut h, insert, nodes, roots)| black_box(h.insert_view_forest(insert, nodes, roots)),
            BatchSize::SmallInput,
        )
    });
    group.bench_function("insert_forest", |b| {
        b.iter_batched(
            || {
                let h = simple_dfg_hugr();
                let (insert, decl, defn) = dfg_calling_defn_decl();
                let roots = [
                    (insert.entrypoint(), h.entrypoint()),
                    (defn.node(), h.module_root()),
                    (decl.node(), h.module_root()),
                ];
                (h, insert, roots)
            },
            |(mut h, insert, roots)| black_box(h.insert_forest(insert, roots)),
            BatchSize::SmallInput,
        )
    });
}

criterion_group! {
    name = benches;
    config = Criterion::default();
    targets = bench_builder, bench_insertion
}
