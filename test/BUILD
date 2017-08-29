# -*- python -*-
# This file contains rules for Bazel; see https://bazel.io/ .

load("//:tools/cpplint.bzl", "cpplint")
load("//tools:dreal.bzl", "dreal_cc_googletest")

cc_test(
    name = "ibex_test",
    srcs = ["ibex_test.cc"],
    deps = [
        "@ibex//:ibex",
    ],
)

dreal_cc_googletest(
    name = "ibex_bitset_test",
    srcs = ["ibex_test.cc"],
    deps = [
        "@ibex//:ibex",
    ],
)

cc_test(
    name = "ibex_polytope_test",
    srcs = [
        "ibex_polytope_test.cc",
    ],
    data = [
        "DiscreteBoundary-0100.bch",
    ],
    deps = [
        "@ibex//:ibex",
    ],
)

dreal_cc_googletest(
    name = "picosat_test",
    srcs = ["picosat_test.cc"],
    deps = [
        "@picosat",
    ],
)

cc_test(
    name = "spdlog_test",
    srcs = ["spdlog_test.cc"],
    deps = [
        "@spdlog//:spdlog",
    ],
)

cpplint()
