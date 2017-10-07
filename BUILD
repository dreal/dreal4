# -*- python -*-
# This file contains rules for Bazel; see https://bazel.io/ .

exports_files([
    "CPPLINT.cfg",
    ".clang-format",
    "VERSION",
])

load("@bazel_tools//tools/build_defs/pkg:pkg.bzl", "pkg_deb", "pkg_tar")

genrule(
    name = "generate_pkg_file",
    srcs = [
        ":VERSION",
    ],
    outs = [
        "dreal.pc",
    ],
    cmd =
        select({
            "@//tools:linux": "$(location //tools:generate_pkg_file_ubuntu) $(location //:VERSION) > $@",
            "@//conditions:default": "$(location //tools:generate_pkg_file_osx) $(location //:VERSION) > $@",
        }),
    tools = [
        "//tools:generate_pkg_file_osx",
        "//tools:generate_pkg_file_ubuntu",
    ],
)

pkg_tar(
    name = "package_pkg_file",
    srcs = ["dreal.pc"],
    extension = "tar.gz",
    package_dir = "/usr/lib/pkgconfig",
    tags = ["manual"],
    visibility = ["//visibility:public"],
)

pkg_tar(
    name = "archive",
    extension = "tar.gz",
    tags = ["manual"],
    deps = [
        ":package_pkg_file",
        "//dreal:package_bin",
        "//dreal:package_headers",
        "//dreal:package_sharedlib",
        "//dreal/smt2:package_headers",
        "//dreal/solver:package_headers",
        "//dreal/symbolic:package_headers",
        "//dreal/util:package_headers",
    ],
)

pkg_deb(
    name = "package_debian",
    architecture = "amd64",
    built_using = "bazel (0.6.1)",
    data = ":archive",
    depends = [
        "bison",
        "coinor-libclp-dev",
        "flex",
        "pkg-config",
        "libibex-dev",
        "libnlopt-dev",
    ],
    description = "SMT solver for nonlinear theories",
    homepage = "http://dreal.github.io",
    maintainer = "Soonho Kong <soonho.kong@gmail.com>",
    package = "dreal",
    tags = ["manual"],
    version_file = "VERSION",
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
