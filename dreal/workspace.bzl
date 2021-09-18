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
load("@dreal//tools:gmp_repository.bzl", "gmp_repository")

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

    gmp_repository(name = "gmp")

    python_configure(name = "local_config_python")

    native.register_toolchains("@local_config_python//:py_toolchain")

    http_archive(
        name = "rules_pkg",
        sha256 = "353b20e8b093d42dd16889c7f918750fb8701c485ac6cceb69a5236500507c27",
        urls = [
            "https://mirror.bazel.build/github.com/bazelbuild/rules_pkg/releases/download/0.5.0/rules_pkg-0.5.0.tar.gz",
            "https://github.com/bazelbuild/rules_pkg/releases/download/0.5.0/rules_pkg-0.5.0.tar.gz",
        ],
    )

    github_archive(
        name = "spdlog",  # MIT
        build_file = str(Label("//tools:spdlog.BUILD.bazel")),
        commit = "v1.8.5",
        repository = "gabime/spdlog",
        sha256 = "944d0bd7c763ac721398dca2bb0f3b5ed16f67cef36810ede5061f35a543b4b8",
    )

    github_archive(
        name = "fmt",  # MIT
        build_file = str(Label("//tools:fmt.BUILD.bazel")),
        commit = "7.1.3",
        repository = "fmtlib/fmt",
        sha256 = "5cae7072042b3043e12d53d50ef404bbb76949dad1de368d7f993a15c8c05ecc",
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
        commit = "v2.7.0",
        repository = "pybind/pybind11",
        sha256 = "6cd73b3d0bf3daf415b5f9b87ca8817cc2e2b64c275d65f9500250f9fee1677e",
    )

    github_archive(
        name = "com_google_absl",  # BSD
        commit = "20200923.3",
        repository = "abseil/abseil-cpp",
        sha256 = "ebe2ad1480d27383e4bf4211e2ca2ef312d5e6a09eba869fd2e8a5c5d553ded2",
    )

    github_archive(
        name = "cds",  # BSL 1.0
        build_file = str(Label("//tools:cds.BUILD.bazel")),
        commit = "v2.3.3",
        repository = "khizmax/libcds",
        sha256 = "f090380ecd6b63a3c2b2f0bdb27260de2ccb22486ef7f47cc1175b70c6e4e388",
    )
