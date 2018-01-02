# -*- python -*-
# This file contains rules for Bazel; see https://bazel.io/ .

load("//:tools/cpplint.bzl", "cpplint")
load(
    "//tools:dreal.bzl",
    "dreal_cc_googletest",
    "dreal_cc_library",
)
load("@bazel_tools//tools/build_defs/pkg:pkg.bzl", "pkg_tar")

# ---------
# Libraries
# ---------
dreal_cc_library(
    name = "api",
    srcs = [
        "api.cc",
    ],
    hdrs = [
        "api.h",
    ],
    visibility = ["//visibility:public"],
    deps = [
        "//dreal/solver",
        "//dreal/symbolic",
        "//dreal/util:assert",
        "//dreal/util:box",
        "//dreal/util:exception",
        "//dreal/util:logging",
    ],
)

# -----
# Tests
# -----
dreal_cc_googletest(
    name = "api_test",
    tags = ["unit"],
    deps = [
        ":api",
    ],
)

# ----------------------
# Header files to expose
# ----------------------
filegroup(
    name = "headers",
    srcs = [
        "api.h",
    ],
    visibility = ["//visibility:public"],
)

pkg_tar(
    name = "package_headers",
    srcs = [
        ":headers",
    ],
    extension = "tar.gz",
    package_dir = "/usr/include/dreal/api",
    tags = ["manual"],
    visibility = ["//visibility:public"],
)

cpplint()
