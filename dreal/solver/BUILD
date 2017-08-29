# -*- python -*-
# This file contains rules for Bazel; see https://bazel.io/ .

load("//:tools/cpplint.bzl", "cpplint")
load("//tools:dreal.bzl", "dreal_cc_googletest", "dreal_cc_library")
load("@bazel_tools//tools/build_defs/pkg:pkg.bzl", "pkg_tar")

package(default_visibility = ["//visibility:public"])

# ---------
# Libraries
# ---------
dreal_cc_library(
    name = "config",
    srcs = [
        "config.cc",
    ],
    hdrs = [
        "config.h",
    ],
)

# We combine context and theory_solver in a single target because they
# have mutual dependencies.
dreal_cc_library(
    name = "solver",
    srcs = [
        "context.cc",
        "theory_solver.cc",
    ],
    hdrs = [
        "context.h",
        "theory_solver.h",
    ],
    deps = [
        ":assertion_filter",
        ":config",
        ":sat_solver",
        "//dreal/contractor",
        "//dreal/icp",
        "//dreal/smt2:logic",
        "//dreal/smt2:sort",
        "//dreal/util:box",
        "//dreal/util:cnfizer",
        "//dreal/util:logging",
        "//dreal/util:nnfizer",
        "//dreal/util:predicate_abstractor",
        "//dreal/util:scoped_vector",
        "//dreal/symbolic:symbolic",
    ],
)

dreal_cc_library(
    name = "sat_solver",
    srcs = [
        "sat_solver.cc",
    ],
    hdrs = [
        "sat_solver.h",
    ],
    deps = [
        "//dreal/util:cnfizer",
        "//dreal/util:logging",
        "//dreal/util:predicate_abstractor",
        "//dreal/symbolic:symbolic",
        "@picosat//:picosat",
    ],
)

dreal_cc_library(
    name = "assertion_filter",
    srcs = [
        "assertion_filter.cc",
    ],
    hdrs = [
        "assertion_filter.h",
    ],
    deps = [
        "//dreal/util:box",
        "//dreal/util:logging",
        "//dreal/symbolic:symbolic",
    ],
)

# -----
# Tests
# -----
dreal_cc_googletest(
    name = "sat_solver_test",
    deps = [
        ":sat_solver",
        "//dreal/util:logging",
    ],
)

dreal_cc_googletest(
    name = "theory_solver_test",
    deps = [
        ":solver",
        "//dreal/util:logging",
    ],
)

# ----------------------
# Header files to expose
# ----------------------
filegroup(
    name = "headers",
    srcs = [
        "config.h",
        "context.h",
    ],
    visibility = ["//visibility:public"],
)

pkg_tar(
    name = "pkg-headers",
    srcs = [
        ":headers",
    ],
    extension = "tar.gz",
    package_dir = "usr/include/dreal/solver",
)

cpplint()
