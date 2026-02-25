# HUGR JSON serialization schema (deprecated)

This folder contains the schema for the serialization of the HUGR objects
compliant with the [JSON Schema](https://json-schema.org/draft/2020-12/release-notes)
specification.

**Note:** This schema is deprecated and will be removed in the future.
See the [envelope encoding specification](https://github.com/quantinuum/hugr/blob/main/specification/serialization.md) for the current serialization format.

The model is generated from the pydantic model in the `hugr` python
package, and is used to validate the serialization format of the Rust
implementation.

A script `generate_schema.py` is provided to regenerate the schema. To update
the schema, run the following command:

```bash
just update-schema
```
