# -*- python -*-

# This file marks a workspace root for the Bazel build system. see
# http://bazel.io/ .

workspace(name = "dreal")

load("//third_party:com_github_robotlocomotion_drake/tools/workspace/github.bzl", "github_archive")

github_archive(
    name = "google_styleguide",  # GOOGLE
    build_file = "//tools:google_styleguide.BUILD.bazel",
    commit = "2723e6b6aad8adb9f85d8b37292a2d421bc6d315",
    repository = "dreal-deps/styleguide",
    sha256 = "71905cbb6a969357ec534d0cd730d8525f4063fdb998e20b1d08b021d31d9095",
)

github_archive(
    name = "pycodestyle",  # Expat
    build_file = "//tools:pycodestyle.BUILD.bazel",
    commit = "368e62cb6c57ff386b5a08659a5a9d2866b80a2f",
    repository = "PyCQA/pycodestyle",
    sha256 = "29cb8bdd6119dc56a6b555896010cb8976bfd2124c6f0ab63ebd84ef2845ca09",
)

github_archive(
    name = "ezoptionparser",  # MIT
    build_file = "//tools:ezoptionparser.BUILD.bazel",
    commit = "b42ee9e166ddc66dd2e02a178592917fb58bbdb7",
    repository = "dreal-deps/ezoptionparser",
    sha256 = "701d9300c02ebf47b184f112b3a7b322003abc8654c96b1762900af35ba447d3",
)

github_archive(
    name = "gtest",  # GOOGLE
    build_file = "//tools:gtest.BUILD.bazel",
    commit = "release-1.8.0",
    repository = "google/googletest",
    sha256 = "58a6f4277ca2bc8565222b3bbd58a177609e9c488e8a72649359ba51450db7d8",
)

load("//dreal:workspace.bzl", "dreal_workspace")

dreal_workspace()
