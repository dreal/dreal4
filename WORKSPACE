workspace(name = "dreal")

load("//third_party:com_github_robotlocomotion_drake/tools/workspace/github.bzl", "github_archive")

github_archive(
    name = "bazel_skylib", # Apache-2.0
    repository = "bazelbuild/bazel-skylib",
    commit = "0.6.0",
    sha256 = "eb5c57e4c12e68c0c20bc774bfbc60a568e800d025557bc4ea022c6479acc867",
)

load("@bazel_skylib//lib:versions.bzl", "versions")

versions.check(minimum_bazel_version = "0.19.2")

github_archive(
    name = "google_styleguide",  # GOOGLE
    build_file = "//tools:google_styleguide.BUILD.bazel",
    commit = "313b6b359086984c8a0bb1d77c195ce3ea3bd78b",
    repository = "dreal-deps/styleguide",  # Use custom version for python3
    sha256 = "ac8214c0c086c186c8d04fb7271792a8bbb3b42c5fee165ff917d908a495109b",
)

github_archive(
    name = "pycodestyle",  # Expat
    build_file = "//tools:pycodestyle.BUILD.bazel",
    commit = "c507b725d9e0bed14505f87cd2397ac7ac489485",
    repository = "PyCQA/pycodestyle",
    sha256 = "b7b206c182f4a4eea6967c6619664e0a91275cd99e929e2bf47b4a8cd48fd218",
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
    commit = "release-1.8.1",
    repository = "google/googletest",
    sha256 = "9bf1fe5182a604b4135edc1a425ae356c9ad15e9b23f9f12a02e80184c3a249c",
)

load("//dreal:workspace.bzl", "dreal_workspace")

dreal_workspace()
