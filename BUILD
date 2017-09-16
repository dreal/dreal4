# -*- python -*-
# This file contains rules for Bazel; see https://bazel.io/ .

exports_files([
    "CPPLINT.cfg",
    ".clang-format",
])

load("@bazel_tools//tools/build_defs/pkg:pkg.bzl", "pkg_deb", "pkg_tar")

pkg_tar(
    name = "package-tar",
    extension = "tar.gz",
    tags = ["manual"],
    deps = [
        "//dreal:pkg-bin",
        "//dreal:pkg-headers",
        "//dreal:pkg-sharedlib",
        "//dreal/smt2:pkg-headers",
        "//dreal/solver:pkg-headers",
        "//dreal/symbolic:pkg-headers",
        "//dreal/util:pkg-headers",
    ],
)

pkg_deb(
    name = "package-deb",
    architecture = "amd64",
    built_using = "bazel (0.5.4)",
    data = ":package-tar",
    depends = [
        "autoconf",
        "automake",
        "bison",
        "coinor-libclp-dev",
        "flex",
        "libtool",
        "pkg-config",
        "libibex-dev",
    ],
    description = "SMT solver for nonlinear theories",
    homepage = "http://dreal.github.io",
    maintainer = "Soonho Kong <soonho.kong@gmail.com>",
    package = "dreal",
    tags = ["manual"],
    version = "4.17.09",
)

load("//tools:dreal.bzl", "dreal_cc_library")

# External users need to include only this target and `dreal/dreal.h` header.
dreal_cc_library(
    name = "dreal",
    srcs = [],
    hdrs = [
        "//dreal:headers",
    ],
    visibility = ["//visibility:public"],
    deps = [
        "//dreal/solver",
        "//dreal/util:box",
    ],
)
