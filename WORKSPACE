workspace(name = "dreal")

load(
    "//third_party/com_github_robotlocomotion_drake:tools/workspace/github.bzl",
    "github_archive",
)

github_archive(
    name = "bazel_skylib",  # Apache-2.0
    commit = "0.9.0",
    repository = "bazelbuild/bazel-skylib",
    sha256 = "9245b0549e88e356cd6a25bf79f97aa19332083890b7ac6481a2affb6ada9752",
)

load("@bazel_skylib//lib:versions.bzl", "versions")

versions.check(minimum_bazel_version = "0.22.0")

github_archive(
    name = "google_styleguide",  # BSD-3
    build_file = "//tools:google_styleguide.BUILD.bazel",
    commit = "adb3500107f409ac5491188ae652ac3f4d03d9d3",  # 20190812
    repository = "cpplint/cpplint",
    sha256 = "d0accc39085ecf61fb81c1b9cce5df889444a6a47ed88dddcc48aa97a79ca6f1",
)

github_archive(
    name = "pycodestyle",  # Expat
    build_file = "//tools:pycodestyle.BUILD.bazel",
    commit = "e71908e1ac65f05cd92b1c6a71ef118f4138b2d7",  # 20190201
    repository = "PyCQA/pycodestyle",
    sha256 = "1b6ce6f278d803ddc5fef599f2eb144c839b50c8f8d4a3950831ad358c870302",
)

github_archive(
    name = "ezoptionparser",  # MIT
    build_file = "//tools:ezoptionparser.BUILD.bazel",
    commit = "94bc81269eb500fb188727777e1ced9b15d97572",
    repository = "dreal-deps/ezoptionparser",
    sha256 = "81f36ac21d7a1c25711da3b9f82ee2cf9588d207328781d9db116a54ba1bf7fb",
)

github_archive(
    name = "com_google_googletest",  # GOOGLE
    commit = "9a502a5b14b4a6160103c1f2c64331772878d86a",  # 20190108
    repository = "google/googletest",
    sha256 = "6b2df434f90104376713c4fb666f2c97a7375edc2e576bcb7dde4eccb291b959",
)

load("//dreal:workspace.bzl", "dreal_workspace")

dreal_workspace()
