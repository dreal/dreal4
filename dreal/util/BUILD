# -*- python -*-
# This file contains rules for Bazel; see https://bazel.io/ .

load("//:tools/cpplint.bzl", "cpplint")
load(
    "//tools:dreal.bzl",
    "dreal_cc_googletest",
    "dreal_cc_library",
)
load("@bazel_tools//tools/build_defs/pkg:pkg.bzl", "pkg_tar")

package(default_visibility = ["//visibility:public"])

# ---------
# Libraries
# ---------
dreal_cc_library(
    name = "assert",
    hdrs = [
        "assert.h",
    ],
)

dreal_cc_library(
    name = "box",
    srcs = [
        "box.cc",
    ],
    hdrs = [
        "box.h",
    ],
    deps = [
        ":assert",
        ":exception",
        ":logging",
        ":math",
        "//dreal/symbolic",
        "@ibex//:ibex",
    ],
)

dreal_cc_library(
    name = "tseitin_cnfizer",
    srcs = [
        "tseitin_cnfizer.cc",
    ],
    hdrs = [
        "tseitin_cnfizer.h",
    ],
    deps = [
        ":assert",
        ":exception",
        ":logging",
        ":naive_cnfizer",
        "//dreal/symbolic",
    ],
)

dreal_cc_library(
    name = "naive_cnfizer",
    srcs = [
        "naive_cnfizer.cc",
    ],
    hdrs = [
        "naive_cnfizer.h",
    ],
    deps = [
        ":assert",
        ":exception",
        ":nnfizer",
        "//dreal/symbolic",
    ],
)

dreal_cc_library(
    name = "exception",
    hdrs = [
        "exception.h",
    ],
    deps = [
        "@fmt",
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
        ":exception",
        ":logging",
        ":math",
        "//dreal/symbolic",
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
        "//dreal/symbolic",
    ],
)

dreal_cc_library(
    name = "option_value",
    hdrs = [
        "option_value.h",
    ],
    deps = [
        "//dreal/symbolic",
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
        "//dreal/symbolic",
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
    hdrs = [
        "scoped_vector.h",
    ],
    deps = [
        ":assert",
        ":exception",
    ],
)

# -----
# Tests
# -----
dreal_cc_googletest(
    name = "box_test",
    tags = ["unit"],
    deps = [
        ":box",
    ],
)

dreal_cc_googletest(
    name = "filesystem_test",
    tags = ["unit"],
    deps = [
        ":filesystem",
    ],
)

dreal_cc_googletest(
    name = "nnfizer_test",
    tags = ["unit"],
    deps = [
        ":nnfizer",
        "//dreal/symbolic:symbolic_test_util",
    ],
)

dreal_cc_googletest(
    name = "option_value_test",
    tags = ["unit"],
    deps = [
        ":option_value",
    ],
)

dreal_cc_googletest(
    name = "predicate_abstractor_test",
    tags = ["unit"],
    deps = [
        ":predicate_abstractor",
        "//dreal/symbolic:symbolic_test_util",
    ],
)

dreal_cc_googletest(
    name = "scoped_vector_test",
    tags = ["unit"],
    deps = [
        ":scoped_vector",
    ],
)

dreal_cc_googletest(
    name = "tseitin_cnfizer_test",
    tags = ["unit"],
    deps = [
        ":tseitin_cnfizer",
        "//dreal/symbolic:symbolic_test_util",
    ],
)

# ----------------------
# Header files to expose
# ----------------------
filegroup(
    name = "headers",
    srcs = [
        "box.h",
        "option_value.h",
    ],
    visibility = ["//visibility:public"],
)

pkg_tar(
    name = "package_headers",
    srcs = [
        ":headers",
    ],
    extension = "tar.gz",
    package_dir = "/usr/include/dreal/util",
    tags = ["manual"],
)

cpplint()
