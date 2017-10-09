# -*- python -*-
# This file contains rules for Bazel; see https://bazel.io/ .

load(":dreal_dr_test.bzl", "dreal_dr_tests")

filegroup(
    name = "dr",
    srcs = glob([
        "*.dr",
        "*.expected",
        "*.option",
    ]),
)

dreal_dr_tests(data = [":dr"])
