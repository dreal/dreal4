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

dreal_cc_googletest(
    name = "symbolic_test",
    tags = ["unittest"],
    deps = [
        ":symbolic",
        ":symbolic_test_util",
    ],
)

# ----------------------
# Header files to expose
# ----------------------
filegroup(
    name = "headers",
    srcs = [
        "symbolic.h",
        "@drake_symbolic//:headers",
    ],
    visibility = ["//visibility:public"],
)

pkg_tar(
    name = "pkg-headers",
    srcs = [
        ":headers",
    ],
    extension = "tar.gz",
    package_dir = "usr/include/dreal/symbolic",
)

cpplint()
