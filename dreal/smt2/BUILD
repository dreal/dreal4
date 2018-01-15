# -*- python -*-
# This file contains rules for Bazel; see https://bazel.io/ .

load("//tools:cpplint.bzl", "cpplint")
load("//tools:dreal.bzl", "dreal_cc_library")
load("@io_kythe_dreal//tools:build_rules/lexyacc.bzl", "genlex", "genyacc")
load("@bazel_tools//tools/build_defs/pkg:pkg.bzl", "pkg_tar")

package(default_visibility = ["//visibility:public"])

genyacc(
    name = "parser",
    srcs = ["parser.yy"],
    outs = [
        "parser.yy.cc",
        "parser.yy.hh",
        # Do not sort the above two.
        "location.hh",
        "position.hh",
        "stack.hh",
    ],
)

genlex(
    name = "scanner",
    srcs = [
        "scanner.ll",
        ":parser",
    ],
    out = "scanner.ll.cc",
)

dreal_cc_library(
    name = "sort",
    srcs = [
        "sort.cc",
    ],
    hdrs = [
        "sort.h",
    ],
    deps = [
        "//dreal/util:exception",
    ],
)

dreal_cc_library(
    name = "logic",
    srcs = [
        "logic.cc",
    ],
    hdrs = [
        "logic.h",
    ],
    deps = [
        "//dreal/util:exception",
    ],
)

dreal_cc_library(
    name = "command",
    srcs = [
        "command.cc",
        "command_cell.cc",
        "command_cell.h",
    ],
    hdrs = [
        "command.h",
    ],
    deps = [
        ":logic",
        "//dreal/symbolic",
    ],
)

dreal_cc_library(
    name = "smt2",
    srcs = [
        "driver.cc",
        "run.cc",
        ":parser",
        ":scanner",
    ],
    hdrs = [
        "driver.h",
        "run.h",
        "scanner.h",
    ],
    deps = [
        ":logic",
        ":sort",
        "//dreal/solver",
        "//dreal/symbolic",
        "//dreal/util:logging",
    ],
)

filegroup(
    name = "headers",
    srcs = [
        "logic.h",
    ],
    visibility = ["//visibility:public"],
)

pkg_tar(
    name = "package_headers",
    srcs = [
        ":headers",
    ],
    extension = "tar.gz",
    package_dir = "/usr/include/dreal/smt2",
    tags = ["manual"],
)

cpplint()
