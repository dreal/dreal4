# -*- python -*-
# This file contains rules for Bazel; see https://bazel.io/ .

exports_files([
    "CPPLINT.cfg",
    ".clang-format",
])

load("@bazel_tools//tools/build_defs/pkg:pkg.bzl", "pkg_tar", "pkg_deb")

pkg_tar(
    name = "cheader-util",
    srcs = [
        "//dreal/util:headers",
    ],
    extension = "tar.gz",
    package_dir = "usr/include/dreal/util",
)

pkg_tar(
    name = "cheader-solver",
    srcs = [
        "//dreal/solver:headers",
    ],
    extension = "tar.gz",
    package_dir = "usr/include/dreal/solver",
)

pkg_tar(
    name = "cheader-smt2",
    srcs = [
        "//dreal/smt2:headers",
    ],
    extension = "tar.gz",
    package_dir = "usr/include/dreal/smt2",
)

pkg_tar(
    name = "clib",
    srcs = [
        "//dreal:libdreal.so",
    ],
    extension = "tar.gz",
    package_dir = "/usr/lib",
)

pkg_tar(
    name = "solver-bin",
    srcs = [
        "//dreal",
    ],
    extension = "tar.gz",
    mode = "0755",
    package_dir = "/usr/bin",
    strip_prefix = "/dreal",
)

pkg_tar(
    name = "package",
    extension = "tar.gz",
    deps = [
        ":cheader-smt2",
        ":cheader-solver",
        ":cheader-util",
        ":clib",
        ":solver-bin",
    ],
)
