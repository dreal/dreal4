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
    name = "box",
    srcs = [
        "box.cc",
    ],
    hdrs = [
        "box.h",
    ],
    deps = [
        ":logging",
        ":math",
        "//dreal/symbolic",
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
        "//dreal/symbolic",
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
)

# -----
# Tests
# -----
dreal_cc_googletest(
    name = "box_test",
    tags = ["unittest"],
    deps = [
        ":box",
    ],
)

dreal_cc_googletest(
    name = "cnfizer_test",
    tags = ["unittest"],
    deps = [
        ":cnfizer",
    ],
)

dreal_cc_googletest(
    name = "nnfizer_test",
    tags = ["unittest"],
    deps = [
        ":nnfizer",
        "//dreal/symbolic:symbolic_test_util",
    ],
)

dreal_cc_googletest(
    name = "predicate_abstractor_test",
    tags = ["unittest"],
    deps = [
        ":predicate_abstractor",
        "//dreal/symbolic:symbolic_test_util",
    ],
)

dreal_cc_googletest(
    name = "scoped_vector_test",
    tags = ["unittest"],
    deps = [
        ":scoped_vector",
    ],
)

# ----------------------
# Header files to expose
# ----------------------
filegroup(
    name = "headers",
    srcs = [
        "box.h",
    ],
    visibility = ["//visibility:public"],
)

pkg_tar(
    name = "pkg-headers",
    srcs = [
        ":headers",
    ],
    extension = "tar.gz",
    package_dir = "/usr/include/dreal/util",
    tags = ["manual"],
)

cpplint()
