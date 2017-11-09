# -*- python -*-
# This file contains rules for Bazel; see https://bazel.io/ .

load("//:tools/cpplint.bzl", "cpplint")
load("//tools:dreal.bzl", "dreal_cc_googletest")

cc_test(
    name = "ibex_test",
    size = "small",
    srcs = ["ibex_test.cc"],
    tags = ["extlib"],
    deps = [
        "@ibex//:ibex",
    ],
)

dreal_cc_googletest(
    name = "ibex_bitset_test",
    srcs = ["ibex_bitset_test.cc"],
    tags = ["extlib"],
    deps = [
        "@ibex//:ibex",
    ],
)

cc_test(
    name = "ibex_polytope_test",
    size = "small",
    srcs = [
        "ibex_polytope_test.cc",
    ],
    data = [
        "DiscreteBoundary-0100.bch",
    ],
    tags = ["extlib"],
    deps = [
        "@ibex//:ibex",
    ],
)

dreal_cc_googletest(
    name = "picosat_test",
    srcs = ["picosat_test.cc"],
    tags = ["extlib"],
    deps = [
        "@picosat",
    ],
)

cc_test(
    name = "spdlog_test",
    size = "small",
    srcs = ["spdlog_test.cc"],
    tags = ["extlib"],
    deps = [
        "@spdlog//:spdlog",
    ],
)

cpplint()
