# HUGR Core Metadata Specification

HUGR nodes can have associated metadata. This is described in the
[Extensible Metadata](./hugr.md#extensible-metadata) section of the specification.

This document describes metadata keys reserved by reference HUGR tooling, which are all
prefixed with "core.".

## Model

The HUGR "model" serialization format has its own notion of node metadata, which
it uses to encode some data that is considered core to the HUGR specification.
It uses a special key to store HUGR metadata, so in some sense it is nested.

Here we list the model-level metadata keys reserved by HUGR tooling; the types refer to
model format types.

| Key                        | Model Type               | Description                                                     |
|----------------------------|--------------------------|-----------------------------------------------------------------|
| core.meta.description      | string                   | Human-readable descriptions.                                    |
| core.entrypoint            | -                        | Marks the module entrypoint.                                    |
| core.order_hint.key        | nat                      | Unique per-node key within a dataflow region used for ordering. |
| core.order_hint.input_key  | nat                      | Order hint key for the region’s input node.                     |
| core.order_hint.output_key | nat                      | Order hint key for the region’s output node.                    |
| core.order_hint.order      | before: nat, after: nat  | Specify ordering of node keys as (before, after).               |
| core.title                 | string                   | Human-readable symbol title preserved across serialization.     |
| compat.meta_json           | name:string, json:string | JSON-encoded metadata for compatibility with hugr-core.         |

The remaining reserved keys are stored under the `compat.meta_json` key, for which the
value types will be given as JSON types below.

## Core
The following reserved HUGR metadata keys use JSON values.

| Key                 | JSON Type                                        | Description                                                                       |
|---------------------|--------------------------------------------------|-----------------------------------------------------------------------------------|
| core.generator      | object { name: string, version: string, ... }    | Identifies the tooling that generated the module. Optional extra fields permitted.|
| core.used_extensions| array of object { name: string, version: string }| Names and versions of all HUGR extensions used in the module.                     |
