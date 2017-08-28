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
    name = "icp",
    srcs = [
        "icp.cc",
    ],
    hdrs = [
        "icp.h",
    ],
    deps = [
        "//dreal/contractor",
        "//dreal/util:box",
        "//dreal/util:evaluator",
        "//dreal/util:symbolic",
    ],
)

dreal_cc_library(
    name = "variable_selector",
    srcs = [
        "variable_selector.cc",
    ],
    hdrs = [
        "variable_selector.h",
    ],
    deps = [
        "//dreal/util:symbolic",
    ],
)

# -----
# Tests
# -----
dreal_cc_googletest(
    name = "icp_test",
    deps = [
        ":icp",
    ],
)

dreal_cc_googletest(
    name = "variable_selector_test",
    deps = [
        ":variable_selector",
    ],
)

cpplint()
