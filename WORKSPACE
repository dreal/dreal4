workspace(name = "dreal")

load("//third_party/com_github_robotlocomotion_drake:tools/workspace/github.bzl", "github_archive")

github_archive(
    name = "bazel_skylib", # Apache-2.0
    repository = "bazelbuild/bazel-skylib",
    commit = "0.8.0",
    sha256 = "2ea8a5ed2b448baf4a6855d3ce049c4c452a6470b1efd1504fdb7c1c134d220a",
)

load("@bazel_skylib//lib:versions.bzl", "versions")

versions.check(minimum_bazel_version = "0.22.0")

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
    commit = "e71908e1ac65f05cd92b1c6a71ef118f4138b2d7",  # 20190201
    repository = "PyCQA/pycodestyle",
    sha256 = "1b6ce6f278d803ddc5fef599f2eb144c839b50c8f8d4a3950831ad358c870302",
)

github_archive(
    name = "ezoptionparser",  # MIT
    build_file = "//tools:ezoptionparser.BUILD.bazel",
    commit = "b42ee9e166ddc66dd2e02a178592917fb58bbdb7",
    repository = "dreal-deps/ezoptionparser",
    sha256 = "701d9300c02ebf47b184f112b3a7b322003abc8654c96b1762900af35ba447d3",
)

github_archive(
    name = "com_google_googletest",  # GOOGLE
    commit = "9a502a5b14b4a6160103c1f2c64331772878d86a",  # 20190108
    repository = "google/googletest",
    sha256 = "6b2df434f90104376713c4fb666f2c97a7375edc2e576bcb7dde4eccb291b959",
)

load("//dreal:workspace.bzl", "dreal_workspace")

dreal_workspace()
