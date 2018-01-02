# -*- python -*-
# This file contains rules for Bazel; see https://bazel.io/ .

load("//:tools/cpplint.bzl", "cpplint")
load(
    "//tools:dreal.bzl",
    "dreal_cc_googletest",
    "dreal_cc_library",
)

package(default_visibility = ["//visibility:public"])

# ---------
# Libraries
# ---------

dreal_cc_library(
    name = "nlopt_optimizer",
    srcs = [
        "nlopt_optimizer.cc",
    ],
    hdrs = [
        "nlopt_optimizer.h",
    ],
    deps = [
        "//dreal/symbolic",
        "//dreal/util:assert",
        "//dreal/util:box",
        "//dreal/util:nnfizer",
        "@nlopt",
    ],
)

# -----
# Tests
# -----
dreal_cc_googletest(
    name = "nlopt_optimizer_test",
    deps = [
        ":nlopt_optimizer",
    ],
)

cpplint()
