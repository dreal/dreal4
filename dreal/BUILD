# -*- python -*-
# This file contains rules for Bazel; see https://bazel.io/ .

load("//:tools/cpplint.bzl", "cpplint")
load(
    "//tools:dreal.bzl",
    "dreal_cc_binary",
)

dreal_cc_binary(
    name = "dreal",
    srcs = [
        "dreal.cc",
    ],
    visibility = ["//visibility:public"],
    deps = [
        "//dreal/smt2:driver",
        "//dreal/util:filesystem",
        "//dreal/util:logging",
        "@ezoptionparser//:ezoptionparser",
    ],
)

cc_binary(
    name = "libdreal.so",
    linkshared = 1,
    visibility = ["//visibility:public"],
    deps = [
        "//dreal/solver",
        "//dreal/util:box",
        "@drake_symbolic",
    ],
)

cpplint()
