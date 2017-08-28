# -*- python -*-
# This file contains rules for Bazel; see https://bazel.io/ .

load(":dreal_smt2_test.bzl", "dreal_smt2_tests")

filegroup(
    name = "smt2",
    srcs = glob([
        "*.smt2",
        "*.expected",
        "*.option",
    ]),
)

dreal_smt2_tests(data = [":smt2"])

# py_test(
#     name = "pytest",
#     args = [
#         "$(location //dreal:dreal)",
#         "dreal/test/01.smt2",
#         "dreal/test/01.smt2.expected",
#     ],
#     srcs = ["test.py"],
#     data = ["//dreal:dreal",
#             ":smt2"],
#     main = "test.py",
#     )
