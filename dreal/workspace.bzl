load("//third_party/com_github_robotlocomotion_drake:tools/workspace/github.bzl", "github_archive")
load("//third_party/com_github_robotlocomotion_drake:tools/workspace/pkg_config.bzl", "pkg_config_repository")
load("//third_party/com_github_tensorflow_tensorflow/py:python_configure.bzl", "python_configure")

def dreal_workspace():
    pkg_config_repository(
        name = "ibex",  # LGPL3
        modname = "ibex",
        pkg_config_paths = [
            # macOS
            "/usr/local/opt/ibex@2.7.4/share/pkgconfig",
            "/usr/local/opt/clp@1.17/lib/pkgconfig",  # dep of ibex, EPL
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

    github_archive(
        name = "spdlog",  # MIT
        repository = "gabime/spdlog",
        commit = "v1.3.1",
        sha256 = "160845266e94db1d4922ef755637f6901266731c4cb3b30b45bf41efa0e6ab70",
        build_file = str(Label("//tools:spdlog.BUILD.bazel")),
    )

    github_archive(
        name = "fmt",  # MIT
        repository = "fmtlib/fmt",
        commit = "6.0.0",
        sha256 = "f1907a58d5e86e6c382e51441d92ad9e23aea63827ba47fd647eacc0d3a16c78",
        build_file = str(Label("//tools:fmt.BUILD.bazel")),
    )

    github_archive(
        name = "picosat",  # MIT
        repository = "dreal-deps/picosat",
        commit = "4ee7aa1d1c645df8fa9daa07f2be17c6d03b35fc",  # v965
        sha256 = "1be461d3659d4e3dc957a718ed295941c38dc822fd22a67f4cb5d180f0b6a7a3",
        build_file = str(Label("//tools:picosat.BUILD.bazel")),
    )

    github_archive(
        name = "pybind11",  # BSD
        repository = "pybind/pybind11",
        commit = "v2.3.0",
        sha256 = "0f34838f2c8024a6765168227ba587b3687729ebf03dc912f88ff75c7aa9cfe8",
        build_file = str(Label("//tools:pybind11.BUILD.bazel")),
    )

    github_archive(
        name = "com_google_absl",  # BSD
        repository = "abseil/abseil-cpp",
        commit = "d78310fe5a82f2e0e6e16509ef8079c8d7e4674e",  # 20190131
        sha256 = "4c2e4194bbddcb5162933e45fe574d2c4e77a2ef00818b8dac0392459707bfff",
    )

    github_archive(
        name = "cds",  # BSL 1.0
        repository = "khizmax/libcds",
        commit = "v2.3.3",
        sha256 = "f090380ecd6b63a3c2b2f0bdb27260de2ccb22486ef7f47cc1175b70c6e4e388",
        build_file = str(Label("//tools:cds.BUILD.bazel")),
    )
