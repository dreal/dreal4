# -*- python -*-
# This file contains rules for Bazel; see https://bazel.io/ .

load("//tools:cpplint.bzl", "cpplint")
load("//tools:dreal.bzl", "dreal_cc_library")
load("//tools:third_party/com_github_google_kythe/tools/build_rules/lexyacc.bzl", "genlex", "genyacc")

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
    name = "dr",
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
        "//dreal/solver",
        "//dreal/symbolic",
        "//dreal/util:scoped_unordered_map",
    ],
)

cpplint()
