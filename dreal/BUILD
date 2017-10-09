# -*- python -*-
# This file contains rules for Bazel; see https://bazel.io/ .

load("//:tools/cpplint.bzl", "cpplint")
load("//tools:dreal.bzl", "dreal_cc_binary", "dreal_cc_library")
load("@bazel_tools//tools/build_defs/pkg:pkg.bzl", "pkg_tar")

genrule(
    name = "generate_version_header",
    srcs = [
        "//:VERSION",
    ],
    outs = [
        "version.h",
    ],
    cmd = "$(location //tools:generate_version_header) $(location //:VERSION) > $@",
    tools = [
        "//tools:generate_version_header",
    ],
)

dreal_cc_library(
    name = "version_header",
    hdrs = [
        "version.h",
    ],
    visibility = [":__subpackages__"],
)

dreal_cc_binary(
    name = "dreal",
    srcs = [
        "dreal_main.cc",
        "dreal_main.h",
    ],
    visibility = ["//visibility:public"],
    deps = [
        "//dreal/dr",
        "//dreal/smt2",
        "//dreal/util:filesystem",
        "//dreal/util:logging",
        "@ezoptionparser//:ezoptionparser",
    ],
)

cc_binary(
    name = "libdreal.so",
    linkopts = select({
        "@dreal//tools:linux": [],
        "@//conditions:default": [
            "-Wl,-install_name,@rpath/libdreal.so",
        ],
    }),
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
        "version.h",
    ],
    visibility = ["//visibility:public"],
)

pkg_tar(
    name = "package_headers",
    srcs = [
        ":headers",
    ],
    extension = "tar.gz",
    package_dir = "/usr/include/dreal",
    tags = ["manual"],
    visibility = ["//visibility:public"],
)

pkg_tar(
    name = "package_bin",
    srcs = [
        ":dreal",
    ],
    extension = "tar.gz",
    mode = "0755",
    package_dir = "/usr/bin",
    strip_prefix = "/dreal",
    tags = ["manual"],
    visibility = ["//visibility:public"],
)

pkg_tar(
    name = "package_sharedlib",
    srcs = [
        ":libdreal.so",
    ],
    extension = "tar.gz",
    package_dir = "/usr/lib",
    tags = ["manual"],
    visibility = ["//visibility:public"],
)

cpplint()
