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
    name = "box",
    srcs = [
        "box.cc",
    ],
    hdrs = [
        "box.h",
    ],
    deps = [
        ":logging",
        ":symbolic",
        "@clp//:clp",
        "@ibex//:ibex",
    ],
)

dreal_cc_library(
    name = "cnfizer",
    srcs = [
        "cnfizer.cc",
    ],
    hdrs = [
        "cnfizer.h",
    ],
    deps = [
        ":symbolic",
    ],
)

dreal_cc_library(
    name = "evaluator",
    srcs = [
        "evaluator.cc",
    ],
    hdrs = [
        "evaluator.h",
    ],
    deps = [
        ":box",
        ":ibex_converter",
        ":logging",
        ":symbolic",
    ],
)

dreal_cc_library(
    name = "filesystem",
    srcs = [
        "filesystem.cc",
    ],
    hdrs = [
        "filesystem.h",
    ],
)

dreal_cc_library(
    name = "ibex_converter",
    srcs = [
        "ibex_converter.cc",
    ],
    hdrs = [
        "ibex_converter.h",
    ],
    deps = [
        ":box",
        ":logging",
        ":math",
        ":symbolic",
        "@clp//:clp",
        "@ibex//:ibex",
    ],
)

dreal_cc_library(
    name = "logging",
    srcs = [
        "logging.cc",
    ],
    hdrs = [
        "logging.h",
    ],
    deps = [
        "@spdlog",
    ],
)

dreal_cc_library(
    name = "math",
    srcs = [
        "math.cc",
    ],
    hdrs = [
        "math.h",
    ],
)

dreal_cc_library(
    name = "nnfizer",
    srcs = [
        "nnfizer.cc",
    ],
    hdrs = [
        "nnfizer.h",
    ],
    deps = [
        ":symbolic",
    ],
)

dreal_cc_library(
    name = "predicate_abstractor",
    srcs = [
        "predicate_abstractor.cc",
    ],
    hdrs = [
        "predicate_abstractor.h",
    ],
    deps = [
        ":symbolic",
    ],
)

dreal_cc_library(
    name = "profiler",
    srcs = [
        "profiler.cc",
    ],
    hdrs = [
        "profiler.h",
    ],
)

dreal_cc_library(
    name = "scoped_vector",
    srcs = [
        "scoped_vector.cc",
    ],
    hdrs = [
        "scoped_vector.h",
    ],
)

dreal_cc_library(
    name = "symbolic",
    srcs = [
        "symbolic.cc",
    ],
    hdrs = [
        "symbolic.h",
    ],
    deps = [
        "@drake_symbolic",
    ],
)

dreal_cc_library(
    name = "symbolic_test_util",
    testonly = 1,
    hdrs = [
        "symbolic_test_util.h",
    ],
    deps = [
        ":symbolic",
    ],
)

# -----
# Tests
# -----
dreal_cc_googletest(
    name = "box_test",
    deps = [
        ":box",
    ],
)

dreal_cc_googletest(
    name = "cnfizer_test",
    deps = [
        ":cnfizer",
    ],
)

dreal_cc_googletest(
    name = "nnfizer_test",
    deps = [
        ":nnfizer",
        "//dreal/util:symbolic_test_util",
    ],
)

dreal_cc_googletest(
    name = "predicate_abstractor_test",
    deps = [
        ":predicate_abstractor",
        "//dreal/util:symbolic_test_util",
    ],
)

dreal_cc_googletest(
    name = "scoped_vector_test",
    deps = [
        ":scoped_vector",
    ],
)

dreal_cc_googletest(
    name = "symbolic_test",
    deps = [
        ":symbolic",
    ],
)

# ----------------------
# Header files to expose
# ----------------------
filegroup(
    name = "headers",
    srcs = [
        "box.h",
        "symbolic.h",
    ],
    visibility = ["//visibility:public"],
)

cpplint()
