from hugr import Hugr, ops, tys
from hugr._serialization.serial_hugr import SerialHugr, serialization_version
from hugr.build.dfg import Dfg
from hugr.build.function import Module
from hugr.package import Package


def test_empty():
    h = SerialHugr(nodes=[], edges=[])
    assert h.model_dump() == {
        "version": serialization_version(),
        "nodes": [],
        "edges": [],
        "metadata": None,
        "encoder": None,
        "entrypoint": None,
    }


def test_children():
    mod = Module()
    mod.declare_function("foo", tys.PolyFuncType([], tys.FunctionType.empty()))

    h = mod.hugr
    assert len(h.children()) == 1

    h2 = Hugr.from_str(h.to_str())

    assert len(h2.children()) == 1


def test_entrypoint():
    dfg = Dfg(tys.Bool)
    noop = dfg.add_op(ops.Noop(tys.Bool), *dfg.inputs())
    dfg.set_outputs(noop)

    h = dfg.hugr
    assert len(h.children()) == 3
    assert h[noop].parent == dfg.to_node()

    func = h[dfg].parent
    assert h[func].op == ops.FuncDefn(
        f_name="main", inputs=[tys.Bool], _outputs=[tys.Bool]
    )
    assert h[func].parent == h.module_root

    # Do a roundtrip, and test all again
    h2 = Hugr.from_str(h.to_str())

    dfg = h2.entrypoint
    assert h2[dfg].op == ops.DFG(inputs=[tys.Bool], _outputs=[tys.Bool])
    assert len(h2.children()) == 3

    noop = h2.children(dfg)[2]
    assert h2[noop].parent == dfg.to_node()

    func = h2[dfg].parent
    assert h2[func].op == ops.FuncDefn(
        f_name="main", inputs=[tys.Bool], _outputs=[tys.Bool]
    )
    assert h2[func].parent == h2.module_root
    assert h2[h2.module_root].op == ops.Module()


def test_params_vars():
    # https://github.com/Quantinuum/hugr/issues/2988
    #
    # This is a regression test for generation of invalid model data from certain guppy-
    # generated HUGRs prior to https://github.com/Quantinuum/hugr/pull/2989. For
    # example:
    #
    # ```guppy
    # N = guppy.nat_var("N")
    #
    # @guppy.declare
    # def foo(_: array[int, N]) -> None: ...
    #
    # pkg = foo.compile()
    # pkg.to_bytes()
    # ```
    #
    # would generate model data like
    #
    # ```
    # (declare-func
    # public
    # foo
    # (param ?_0 core.nat)
    # (core.fn
    #   [(collections.borrow_arr.borrow_array ?0 (arithmetic.int.types.int 6))]
    #   [(collections.borrow_arr.borrow_array ?0 (arithmetic.int.types.int 6))]))
    # ```
    #
    # leading to `ValueError: unknown var: ?0`, as the type parameter in the signature
    # of the function (representing the size of the array) was incorrectly named.

    pkg = Package.from_bytes(
        b"HUGRiHJv?@"
        + b"""{
    "modules":
    [
        {
            "version": "live",
            "nodes":
            [
                {"parent": 0, "op": "Module"},
                {
                    "parent": 0,
                    "op": "FuncDecl",
                    "name": "foo",
                    "signature":
                    {
                        "params": [{"tp": "BoundedNat", "bound": null}],
                        "body":
                        {
                            "t": "G",
                            "input":
                            [
                                {
                                    "t": "Opaque",
                                    "extension": "collections.array",
                                    "id": "array",
                                    "args":
                                    [
                                        {
                                            "tya": "Variable",
                                            "idx": 0,
                                            "cached_decl":
                                            {
                                                "tp": "BoundedNat",
                                                "bound": null
                                            }
                                        },
                                        {
                                            "tya": "Type",
                                            "ty":
                                            {
                                                "t": "Opaque",
                                                "extension": "arithmetic.int.types",
                                                "id": "int",
                                                "args": [{"tya": "BoundedNat", "n": 6}],
                                                "bound": "C"
                                            }
                                        }
                                    ],
                                    "bound": "A"
                                }
                            ],
                            "output":
                            [
                                {
                                    "t": "Opaque",
                                    "extension": "collections.array",
                                    "id": "array",
                                    "args":
                                    [
                                        {
                                            "tya": "Variable",
                                            "idx": 0,
                                            "cached_decl":
                                            {
                                                "tp": "BoundedNat",
                                                "bound": null
                                            }
                                        },
                                        {
                                            "tya": "Type",
                                            "ty":
                                            {
                                                "t": "Opaque",
                                                "extension": "arithmetic.int.types",
                                                "id": "int",
                                                "args": [{"tya": "BoundedNat", "n": 6}],
                                                "bound": "C"
                                            }
                                        }
                                    ],
                                    "bound": "A"
                                }
                            ]
                        }
                    },
                    "visibility": "Public"
                }
            ],
            "edges": [],
            "encoder": null,
            "entrypoint": 0
        }
    ],
    "extensions": []
}"""
    )
    data = pkg.to_bytes()
    pkg1 = Package.from_bytes(data)
    assert pkg.to_model() == pkg1.to_model()
