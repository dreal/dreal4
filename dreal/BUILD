# -*- python -*-
# This file contains rules for Bazel; see https://bazel.io/ .

load("//:tools/cpplint.bzl", "cpplint")
load("//tools:dreal.bzl", "dreal_cc_binary")
load("@bazel_tools//tools/build_defs/pkg:pkg.bzl", "pkg_tar")

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

# ----------------------
# Header files to expose
# ----------------------
filegroup(
    name = "headers",
    srcs = [
        "dreal.h",
    ],
    visibility = ["//visibility:public"],
)

pkg_tar(
    name = "pkg-headers",
    srcs = [
        ":headers",
    ],
    extension = "tar.gz",
    package_dir = "usr/include/dreal",
    visibility = ["//visibility:public"],
)

pkg_tar(
    name = "pkg-bin",
    srcs = [
        ":dreal",
    ],
    extension = "tar.gz",
    mode = "0755",
    package_dir = "/usr/bin",
    strip_prefix = "/dreal",
    visibility = ["//visibility:public"],
)

pkg_tar(
    name = "pkg-sharedlib",
    srcs = [
        ":libdreal.so",
    ],
    extension = "tar.gz",
    package_dir = "/usr/lib",
    visibility = ["//visibility:public"],
)

cpplint()
