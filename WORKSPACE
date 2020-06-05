workspace(name = "dreal")

load(
    "//third_party/com_github_robotlocomotion_drake:tools/workspace/github.bzl",
    "github_archive",
)
load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

github_archive(
    name = "bazel_skylib",  # Apache-2.0
    commit = "1.0.2",
    repository = "bazelbuild/bazel-skylib",
    sha256 = "e5d90f0ec952883d56747b7604e2a15ee36e288bb556c3d0ed33e818a4d971f2",
)

load("@bazel_skylib//lib:versions.bzl", "versions")

versions.check(minimum_bazel_version = "0.29.0")

github_archive(
    name = "google_styleguide",  # BSD-3
    build_file = "//tools:google_styleguide.BUILD.bazel",
    commit = "1.5.0",
    repository = "cpplint/cpplint",
    sha256 = "20c440f6fe612180e79ee370b85f56a66b177fd122ad7e2cb911527857dae4ad",
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
    name = "rules_python",
    sha256 = "aa96a691d3a8177f3215b14b0edc9641787abaaa30363a080165d06ab65e1161",
    url = "https://github.com/bazelbuild/rules_python/releases/download/0.0.1/rules_python-0.0.1.tar.gz",
)

load("@rules_python//python:repositories.bzl", "py_repositories")

py_repositories()

load("//dreal:workspace.bzl", "dreal_workspace")

dreal_workspace()
