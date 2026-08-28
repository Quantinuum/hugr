//! Benchmarks
#![allow(dead_code)]

mod benchmarks;
mod examples;

use criterion::criterion_main;

criterion_main! {
    benchmarks::hugr::benches,
    benchmarks::serialization::benches,
    benchmarks::subgraph::benches,
    benchmarks::types::benches,
}
