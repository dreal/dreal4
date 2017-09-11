
# -*- python -*-

# This file marks a workspace root for the Bazel build system. see
# http://bazel.io/ .

workspace(name = "dreal")

# Buildifier setup -- BEGIN
http_archive(
    name = "io_bazel_rules_go",  # Apache 2.0
    sha256 = "84dc11091f5209bf24f1ee710ff0c645f86016bfdbbb11fb831580e95f1975c6",
    strip_prefix = "rules_go-2e319588571f20fdaaf83058b690abd32f596e89",
    urls = [
        "http://mirror.bazel.build/github.com/bazelbuild/rules_go/archive/2e319588571f20fdaaf83058b690abd32f596e89.tar.gz",
        "https://github.com/bazelbuild/rules_go/archive/2e319588571f20fdaaf83058b690abd32f596e89.tar.gz",
    ],
)
load(
    "@io_bazel_rules_go//go:def.bzl",
    "go_rules_dependencies",
    "go_register_toolchains",
    "go_repository",
)
load("@io_bazel_rules_go//proto:go_proto_library.bzl", "go_proto_repositories")
go_rules_dependencies()
go_register_toolchains()
go_proto_repositories()
# Buildifier setup -- END

load("//tools:github.bzl", "github_archive")

github_archive(
    name = "io_kythe_dreal", # Apache-2.0
    repository = "dreal-deps/kythe",
    commit = "333ddf386fda81fb3f9962e54eb30a67b14315db",
    sha256 = "9e8db92c3eb605be5a74daf6f0621298a487b6b2e4f279e68ddf8b513826491b",
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
