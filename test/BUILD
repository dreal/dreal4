# -*- python -*-
# This file contains rules for Bazel; see https://bazel.io/ .

load("//:tools/cpplint.bzl", "cpplint")

cc_test(
    name = "ibex_test",
    srcs = ["ibex_test.cc"],
    deps = [
        "@clp//:clp",
        "@ibex//:ibex",
    ],
)

cc_test(
    name = "ibex_bitset_test",
    srcs = ["ibex_test.cc"],
    deps = [
        "@clp//:clp",
        "@gtest//:main",
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
        "@clp//:clp",
        "@ibex//:ibex",
    ],
)

# cc_test(
#     name = "minisat_test",
#     srcs = ["minisat_test.cc"],
#     deps = [
#         "@gtest//:main",
#         "@minisat//:minisat",
#     ],
# )

cc_test(
    name = "picosat_test",
    srcs = ["picosat_test.cc"],
    deps = [
        "@gtest//:main",
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
