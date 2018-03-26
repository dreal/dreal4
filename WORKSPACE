# -*- python -*-

# This file marks a workspace root for the Bazel build system. see
# http://bazel.io/ .

workspace(name = "dreal")

load("//tools:github.bzl", "github_archive")

github_archive(
    name = "google_styleguide",  # GOOGLE
    build_file = "//tools:google_styleguide.BUILD",
    commit = "209d38166b1a56b177de486d894d39ae6822eee6",
    repository = "google/styleguide",
    sha256 = "7f2026b7085c32aaf99e7588f0c49b05a126ea1e2e6a635dc60b67dc5c789cb0",
)

github_archive(
    name = "pycodestyle",  # Expat
    build_file = "//tools:pycodestyle.BUILD",
    commit = "368e62cb6c57ff386b5a08659a5a9d2866b80a2f",
    repository = "PyCQA/pycodestyle",
    sha256 = "29cb8bdd6119dc56a6b555896010cb8976bfd2124c6f0ab63ebd84ef2845ca09",
)

github_archive(
    name = "ezoptionparser",  # MIT
    build_file = "//tools:ezoptionparser.BUILD",
    commit = "b42ee9e166ddc66dd2e02a178592917fb58bbdb7",
    repository = "dreal-deps/ezoptionparser",
    sha256 = "701d9300c02ebf47b184f112b3a7b322003abc8654c96b1762900af35ba447d3",
)

github_archive(
    name = "gtest",  # GOOGLE
    build_file = "//tools:gtest.BUILD",
    commit = "release-1.8.0",
    repository = "google/googletest",
    sha256 = "58a6f4277ca2bc8565222b3bbd58a177609e9c488e8a72649359ba51450db7d8",
)

load("//dreal:workspace.bzl", "dreal_workspace")

dreal_workspace()
