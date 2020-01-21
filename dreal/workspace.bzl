load(
    "//third_party/com_github_robotlocomotion_drake:tools/workspace/github.bzl",
    "github_archive",
)
load(
    "//third_party/com_github_robotlocomotion_drake:tools/workspace/pkg_config.bzl",
    "pkg_config_repository",
)
load(
    "//third_party/com_github_tensorflow_tensorflow/py:python_configure.bzl",
    "python_configure",
)
load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

def dreal_workspace():
    pkg_config_repository(
        name = "ibex",  # LGPL3
        modname = "ibex",
        pkg_config_paths = [
            # macOS
            "/usr/local/opt/clp/lib/pkgconfig",
            "/usr/local/opt/coinutils/lib/pkgconfig",
            "/usr/local/opt/ibex@2.7.4/share/pkgconfig",
            # Linux
            "/opt/libibex/2.7.4/share/pkgconfig",
        ],
    )
    pkg_config_repository(
        name = "nlopt",  # LGPL2 + MIT
        modname = "nlopt",
        pkg_config_paths = [
            "/usr/local/opt/nlopt/lib/pkgconfig",
        ],
    )
    python_configure(name = "local_config_python")

    http_archive(
        name = "rules_pkg",
        sha256 = "4ba8f4ab0ff85f2484287ab06c0d871dcb31cc54d439457d28fd4ae14b18450a",
        url = "https://github.com/bazelbuild/rules_pkg/releases/download/0.2.4/rules_pkg-0.2.4.tar.gz",
    )

    github_archive(
        name = "spdlog",  # MIT
        build_file = str(Label("//tools:spdlog.BUILD.bazel")),
        commit = "v1.5.0",
        repository = "gabime/spdlog",
        sha256 = "b38e0bbef7faac2b82fed550a0c19b0d4e7f6737d5321d4fd8f216b80f8aee8a",
    )

    github_archive(
        name = "fmt",  # MIT
        build_file = str(Label("//tools:fmt.BUILD.bazel")),
        commit = "6.1.2",
        repository = "fmtlib/fmt",
        sha256 = "1cafc80701b746085dddf41bd9193e6d35089e1c6ec1940e037fcb9c98f62365",
    )

    github_archive(
        name = "picosat",  # MIT
        build_file = str(Label("//tools:picosat.BUILD.bazel")),
        commit = "4ee7aa1d1c645df8fa9daa07f2be17c6d03b35fc",  # v965
        repository = "dreal-deps/picosat",
        sha256 = "1be461d3659d4e3dc957a718ed295941c38dc822fd22a67f4cb5d180f0b6a7a3",
    )

    github_archive(
        name = "pybind11",  # BSD
        build_file = str(Label("//tools:pybind11.BUILD.bazel")),
        commit = "v2.4.3",
        repository = "pybind/pybind11",
        sha256 = "1eed57bc6863190e35637290f97a20c81cfe4d9090ac0a24f3bbf08f265eb71d",
    )

    github_archive(
        name = "com_google_absl",  # BSD
        commit = "d78310fe5a82f2e0e6e16509ef8079c8d7e4674e",  # 20190131
        repository = "abseil/abseil-cpp",
        sha256 = "4c2e4194bbddcb5162933e45fe574d2c4e77a2ef00818b8dac0392459707bfff",
    )

    github_archive(
        name = "cds",  # BSL 1.0
        build_file = str(Label("//tools:cds.BUILD.bazel")),
        commit = "v2.3.3",
        repository = "khizmax/libcds",
        sha256 = "f090380ecd6b63a3c2b2f0bdb27260de2ccb22486ef7f47cc1175b70c6e4e388",
    )
