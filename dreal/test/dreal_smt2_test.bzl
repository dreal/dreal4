# -*- python -*-
# This file contains rules for Bazel; see drake/doc/bazel.rst.

# def dreal_smt2_tests(data):
#     for smt2 in native.glob(["*.smt2"]):
#         prefix = "dreal/test/"
#         native.py_test(
#             args = ["$(location //dreal:dreal)",
#                     prefix + smt2],
#             name = "run_" + smt2,
#             srcs = ["test.py"],
#             data = data,
#             deps = ["//dreal:dreal"],
#         )

def dreal_smt2_tests(data):
    prefix = "dreal/test/"
    for smt2 in native.glob(["*.smt2"]):
        native.py_test(
            name = "run_" + smt2,
            args = [
                "$(location //dreal:dreal)",
                prefix + smt2,
                prefix + smt2 + ".expected",
            ],
            srcs = ["test.py"],
            data = ["//dreal:dreal",
                    ":smt2"],
            main = "test.py",
        )
