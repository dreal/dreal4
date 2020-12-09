workspace(name = "dreal")

load(
    "//third_party/com_github_robotlocomotion_drake:tools/workspace/github.bzl",
    "github_archive",
)
load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

github_archive(
    name = "bazel_skylib",  # Apache-2.0
    commit = "1.0.3",
    repository = "bazelbuild/bazel-skylib",
    sha256 = "7ac0fa88c0c4ad6f5b9ffb5e09ef81e235492c873659e6bb99efb89d11246bcb",
)

load("@bazel_skylib//lib:versions.bzl", "versions")

versions.check(minimum_bazel_version = "3.0.0")

github_archive(
    name = "google_styleguide",  # BSD-3
    build_file = "//tools:google_styleguide.BUILD.bazel",
    commit = "1.5.3",
    repository = "cpplint/cpplint",
    sha256 = "447508de65fc221c2d17655bc0ac7083ce20bcc3d3d1ec46ff4fb3484f9028f3",
)

github_archive(
    name = "pycodestyle",  # Expat
    build_file = "//tools:pycodestyle.BUILD.bazel",
    commit = "2.6.0",
    repository = "PyCQA/pycodestyle",
    sha256 = "08347fbc48cc92afd33117c1e8af9b99b292a4e5889f6b776f402e062fc39c97",
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
    commit = "cb44c86c1aaf31b26797728e93acc950c01dbd5b",  # 2020/06/02
    repository = "google/googletest",
    sha256 = "9a1427fc06bfe11dec4fa7489026a3d0983f64123805c4ac922896de92004a7f",
)

http_archive(
    name = "rules_python",  # Apache-2.0
    sha256 = "b6d46438523a3ec0f3cead544190ee13223a52f6a6765a29eae7b7cc24cc83a0",
    url = "https://github.com/bazelbuild/rules_python/releases/download/0.1.0/rules_python-0.1.0.tar.gz",
)

load("@rules_python//python:repositories.bzl", "py_repositories")

py_repositories()

load("//dreal:workspace.bzl", "dreal_workspace")

dreal_workspace()
