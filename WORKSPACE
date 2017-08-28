# -*- python -*-

# This file marks a workspace root for the Bazel build system. see
# http://bazel.io/ .

workspace(name = "dreal")

load("//tools:github.bzl", "github_archive")

local_repository(
    name = "kythe",
    path = "tools/third_party/kythe",
)

load("@kythe//tools/build_rules/config:pkg_config.bzl", "pkg_config_package")

pkg_config_package(
    name = "ibex",
    modname = "ibex",
)

# TODO(soonho): clp dependency should be embedded in ibex.
pkg_config_package(
    name = "clp",
    modname = "clp",
)

# Necessary for buildifier.
github_archive(
    name = "io_bazel_rules_go", # Apache 2.0
    repository = "bazelbuild/rules_go",
    commit = "0.4.2",
    sha256 = "713c4dd4cfafdf34ed4bdd15eaffc66b15a73dcfbae54a3f109b360c54ecc096",
)

# Necessary for buildifier.
load("@io_bazel_rules_go//go:def.bzl", "go_repositories", "new_go_repository")

# Necessary for buildifier.
go_repositories()

# Necessary for buildifier.
new_go_repository(
    name = "org_golang_x_tools",
    commit = "3d92dd60033c312e3ae7cac319c792271cf67e37",
    importpath = "golang.org/x/tools",
)

github_archive(
    name = "com_github_bazelbuild_buildtools", # Apache 2.0
    repository = "bazelbuild/buildtools",
    commit = "45633988bb2b956f77c1075c4bc551ea3d7798b3", # 0.4.5
    sha256 = "73772adde342f221ad5bc8c4ba7643b00f66ed76a978af4aae5d2c0af6d47e68",
)

github_archive(
    name = "google_styleguide", # GOOGLE
    repository = "google/styleguide",
    commit = "15f2836d9fea3835d541d4d327ccf053d4052822",
    sha256 = "448d528447e7e8c363b3757605ecfd6e8a779a6ff2dd4bb321e4739aa1a59981",
    build_file = "//tools:google_styleguide.BUILD",
)
github_archive(
    name = "gtest", # GOOGLE
    repository = "google/googletest",
    commit = "release-1.8.0",
    sha256 = "58a6f4277ca2bc8565222b3bbd58a177609e9c488e8a72649359ba51450db7d8",
    build_file = "//tools:gtest.BUILD",
)

load("//dreal:workspace.bzl", "dreal_workspace")
dreal_workspace()
