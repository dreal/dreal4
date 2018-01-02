# -*- python -*-
# This file contains rules for Bazel; see https://bazel.io/ .

load("//:tools/cpplint.bzl", "cpplint")
load(
    "//tools:dreal.bzl",
    "dreal_cc_binary",
)

dreal_cc_binary(
    name = "check_lyapunov",
    srcs = [
        "check_lyapunov.cc",
    ],
    visibility = ["//visibility:public"],
    deps = [
        "//dreal/api",
        "//dreal/solver",
        "//dreal/util:assert",
    ],
)

dreal_cc_binary(
    name = "synthesize_lyapunov",
    srcs = [
        "synthesize_lyapunov.cc",
    ],
    visibility = ["//visibility:public"],
    deps = [
        "//dreal/api",
        "//dreal/solver",
        "//dreal/util:assert",
    ],
)

dreal_cc_binary(
    name = "sat_checker",
    srcs = [
        "sat_checker.cc",
    ],
    visibility = ["//visibility:public"],
    deps = [
        "//dreal/solver",
    ],
)

cpplint()
