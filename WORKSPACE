workspace(name = "dreal")

load("//third_party:com_github_robotlocomotion_drake/tools/workspace/github.bzl", "github_archive")

github_archive(
    name = "google_styleguide",  # GOOGLE
    build_file = "//tools:google_styleguide.BUILD.bazel",
    commit = "ab48617e00be9d111804bd3715dd7b5f5732c9a3",
    repository = "google/styleguide",
    sha256 = "fed315ad645c17cac86af58b157b1237c386515a181de8caad0d6f1fb9d1e563",
)

github_archive(
    name = "pycodestyle",  # Expat
    build_file = "//tools:pycodestyle.BUILD.bazel",
    commit = "566cdc0cb22e5530902e456d0b315403ebab980c",
    repository = "PyCQA/pycodestyle",
    sha256 = "32fdb7320ed8ee47f522245371c30b783dddd80da0a801db4232209554eb0472",
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
