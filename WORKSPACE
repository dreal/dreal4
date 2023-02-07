workspace(name = "dreal")

load(
    "//third_party/com_github_robotlocomotion_drake:tools/workspace/github.bzl",
    "github_archive",
)
load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

github_archive(
    name = "bazel_skylib",  # Apache-2.0
    commit = "1.4.0",
    repository = "bazelbuild/bazel-skylib",
    sha256 = "4dd05f44200db3b78f72f56ebd8b102d5bcdc17c0299955d4eb20c38c6f07cd7",
)

load("@bazel_skylib//lib:versions.bzl", "versions")

versions.check(minimum_bazel_version = "4.2.1")

github_archive(
    name = "google_styleguide",  # BSD-3
    build_file = "//tools:google_styleguide.BUILD.bazel",
    commit = "1.6.1",
    repository = "cpplint/cpplint",
    sha256 = "7be47998c4bd590e229cf94f3312c46563d3ee35ea037b4ed389720f510029d6",
)

github_archive(
    name = "pycodestyle",  # Expat
    build_file = "//tools:pycodestyle.BUILD.bazel",
    commit = "2.10.0",
    repository = "PyCQA/pycodestyle",
    sha256 = "a7306561f1ddf7bc00419b9f0d698d312a8eaa173b834e7c8e4ff32db5efd27f",
)

github_archive(
    name = "ezoptionparser",  # MIT
    build_file = "//tools:ezoptionparser.BUILD.bazel",
    commit = "5bb9214fc26bf14cea071411216e23799cabd0da",
    repository = "dreal-deps/ezoptionparser",
    sha256 = "7349f3091bd05a675a61b61350536f32da77578d3bfb629e2ed5bc31b7a4fa2c",
)

github_archive(
    name = "com_google_googletest",  # GOOGLE
    commit = "release-1.12.1",
    repository = "google/googletest",
    sha256 = "81964fe578e9bd7c94dfdb09c8e4d6e6759e19967e397dbea48d1c10e45d0df2",
)

# Note: Dependency of rules_pkg in dreal/workspace.bzl
http_archive(
    name = "rules_python",  # Apache-2.0
    sha256 = "8c15896f6686beb5c631a4459a3aa8392daccaab805ea899c9d14215074b60ef",
    strip_prefix = "rules_python-0.17.3",
    url = "https://github.com/bazelbuild/rules_python/archive/refs/tags/0.17.3.tar.gz",
)

load("//dreal:workspace.bzl", "dreal_workspace")

dreal_workspace()
