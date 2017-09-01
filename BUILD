# -*- python -*-
# This file contains rules for Bazel; see https://bazel.io/ .

exports_files([
    "CPPLINT.cfg",
    ".clang-format",
])

load("@bazel_tools//tools/build_defs/pkg:pkg.bzl", "pkg_tar")

pkg_tar(
    name = "package",
    extension = "tar.gz",
    deps = [
        "//dreal:pkg-bin",
        "//dreal:pkg-headers",
        "//dreal:pkg-sharedlib",
        "//dreal/smt2:pkg-headers",
        "//dreal/solver:pkg-headers",
        "//dreal/symbolic:pkg-headers",
        "//dreal/util:pkg-headers",
    ],
)

load("//tools:dreal.bzl", "dreal_cc_library")

# External users need to include only this target and `dreal/dreal.h` header.
dreal_cc_library(
    name = "dreal",
    srcs = [],
    hdrs = [
        "//dreal:headers",
    ],
    visibility = ["//visibility:public"],
    deps = [
        "//dreal/solver",
        "//dreal/util:box",
    ],
)
