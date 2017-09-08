
# -*- python -*-

# This file marks a workspace root for the Bazel build system. see
# http://bazel.io/ .

workspace(name = "dreal")

# Buildifier setup -- BEGIN
http_archive(
    name = "io_bazel_rules_go",  # Apache 2.0
    sha256 = "1e8e662ab93eca94beb6c690b8fd41347835e8ce0f3c4f71708af4b6673dd171",
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
    sha256 = "63d59334434f6d84c89da46d04305736fa58c29282f9d9372580dc0957a61b70",
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
