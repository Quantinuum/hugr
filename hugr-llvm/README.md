# hugr-llvm

[![build_status][]](https://github.com/quantinuum/hugr/actions)
[![codecov](https://codecov.io/github/quantinuum/hugr/graph/badge.svg?token=TN3DSNHF43)](https://codecov.io/github/quantinuum/hugr)
[![msrv][]](https://github.com/quantinuum/hugr/tree/main/hugr-llvm)

A general, extensible, rust crate for lowering `HUGR`s into `LLVM` IR. Built on [hugr][], [inkwell][], and [llvm][].

## Usage

You'll need to point your `Cargo.toml` to use a single LLVM version feature flag corresponding to your LLVM version, by calling

```bash
cargo add hugr-llvm --features llvm21-1
```

At present only `llvm21-1` is supported but we expect to introduce supported versions as required. Contributions are welcome.

See the [llvm-sys][] crate for details on how to use your preferred llvm installation.

### Shared pointers

Register `CodegenExtsBuilder::add_default_ptr_extensions()` to lower the `ptr`
extension with libc `malloc`/`free` and no-op mutex hooks. These defaults require
that accesses to the same cell do not execute concurrently.

For concurrent execution or a target-specific allocator, implement
`extension::ptr::PtrCodegen` and register it with `add_ptr_extensions(hooks)`.
Allocation/free and lock/unlock are independently overridable. Allocation returns
an opaque handle with any mutex initialized; free owns its teardown. The
`emit_get_ptr` hook projects the payload (reference count and HUGR value) from
that handle, leaving the runtime storage layout under your control.
`Map` holds the mutex throughout its callback, which must not access the same
cell through another handle.

Thread the returned pointer through successive operations to order them.
Operations on duplicated handles have unspecified relative order, even when
mutex hooks serialize their execution.

## Recent Changes

See [CHANGELOG](CHANGELOG.md) for a list of changes. The minimum supported rust
version will only change on major releases.

## Developing hugr-llvm

See [DEVELOPMENT](../DEVELOPMENT.md) for instructions on setting up the development environment.

## License

This project is licensed under Apache License, Version 2.0 ([LICENCE](LICENCE) or <http://www.apache.org/licenses/LICENSE-2.0>).

  [build_status]: https://github.com/quantinuum/hugr/actions/workflows/ci-rs.yml/badge.svg?branch=main
  [msrv]: https://img.shields.io/crates/msrv/hugr-llvm
  [hugr]: https://lib.rs/crates/hugr
  [inkwell]: https://thedan64.github.io/inkwell/inkwell/index.html
  [llvm-sys]: https://crates.io/crates/llvm-sys
  [llvm]: https://llvm.org/
