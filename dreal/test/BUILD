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
