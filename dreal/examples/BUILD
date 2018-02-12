# -*- python -*-
# This file contains rules for Bazel; see https://bazel.io/ .

load("//:tools/cpplint.bzl", "cpplint")
load(
    "//tools:dreal.bzl",
    "dreal_cc_binary",
    "dreal_cc_library",
)

dreal_cc_library(
    name = "control",
    srcs = [
        "control.cc",
    ],
    hdrs = [
        "control.h",
    ],
    deps = [
        "//dreal/api",
        "//dreal/solver",
        "//dreal/util:assert",
    ],
)

dreal_cc_binary(
    name = "check_lyapunov",
    srcs = [
        "check_lyapunov.cc",
    ],
    visibility = ["//visibility:public"],
    deps = [
        ":control",
    ],
)

dreal_cc_binary(
    name = "synthesize_lyapunov_simple",
    srcs = [
        "synthesize_lyapunov_simple.cc",
    ],
    visibility = ["//visibility:public"],
    deps = [
        ":control",
    ],
)

dreal_cc_binary(
    name = "synthesize_lyapunov_normalized_pendulum",
    srcs = [
        "synthesize_lyapunov_normalized_pendulum.cc",
    ],
    visibility = ["//visibility:public"],
    deps = [
        ":control",
    ],
)

dreal_cc_binary(
    name = "synthesize_lyapunov_damped_mathieu",
    srcs = [
        "synthesize_lyapunov_damped_mathieu.cc",
    ],
    visibility = ["//visibility:public"],
    deps = [
        ":control",
    ],
)

dreal_cc_binary(
    name = "synthesize_lyapunov_moore_greitzer",
    srcs = [
        "synthesize_lyapunov_moore_greitzer.cc",
    ],
    visibility = ["//visibility:public"],
    deps = [
        ":control",
    ],
)

dreal_cc_binary(
    name = "synthesize_lyapunov_power_train",
    srcs = [
        "synthesize_lyapunov_power_train.cc",
    ],
    visibility = ["//visibility:public"],
    deps = [
        ":control",
    ],
)

dreal_cc_binary(
    name = "program_synthesis_abs",
    srcs = [
        "program_synthesis_abs.cc",
    ],
    visibility = ["//visibility:public"],
    deps = [
        "//dreal/api",
    ],
)

cpplint()
