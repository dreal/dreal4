# -*- python -*-
load("//third_party:com_github_robotlocomotion_drake/tools/workspace/github.bzl", "github_archive")
load("//third_party:com_github_robotlocomotion_drake/tools/workspace/pkg_config.bzl", "pkg_config_repository")

def dreal_workspace():
    pkg_config_repository(
        name = "ibex", # LGPL3
        modname = "ibex",
        pkg_config_paths = [
            # macOS
            "/usr/local/opt/ibex@2.6.5/share/pkgconfig",
            "/usr/local/opt/clp/lib/pkgconfig",  # dep of ibex, EPL
            "/usr/local/opt/coinutils/lib/pkgconfig",  # dep of clp, EPL
            # Linux
            "/opt/libibex/2.6.5/share/pkgconfig",
        ],
    )
    pkg_config_repository(
        name = "nlopt",  # LGPL2 + MIT
        modname = "nlopt",
        pkg_config_paths = [
            "/usr/local/opt/nlopt/lib/pkgconfig",
        ]
    )
    pkg_config_repository(
        name = "python2",
        modname = "python2",
        pkg_config_paths = [
            "/usr/local/opt/python@2/lib/pkgconfig",
        ]
    )
    # We do not use this one, yet.
    pkg_config_repository(
        name = "python3",
        modname = "python3",
        pkg_config_paths = [
            "/usr/local/opt/python@3/lib/pkgconfig",
        ]
    )
    github_archive(
        name = "drake_symbolic", # BSD
        repository = "dreal-deps/drake-symbolic",
        commit = "6ec11a2ce74f633bca5b9125dfa1a0d2e4c8b2f3",
        sha256 = "58f0acc954c8637bcfd2e1cce4a5831c4c62dce015660bda6751151a1a1a0609",
    )
    github_archive(
        name = "spdlog", # MIT
        repository = "gabime/spdlog",
        commit = "v0.13.0",
        sha256 = "d798a6ca19165f0a18a43938859359269f5a07fd8e0eb83ab8674739c9e8f361",
        build_file = str(Label("//tools:spdlog.BUILD.bazel")),
    )
    github_archive(
        name = "fmt", # BSD2
        repository = "fmtlib/fmt",
        commit = "4.1.0",
        sha256 = "46628a2f068d0e33c716be0ed9dcae4370242df135aed663a180b9fd8e36733d",
        build_file = str(Label("//tools:fmt.BUILD.bazel")),
    )
    github_archive(
        name = "picosat", # MIT
        repository = "dreal-deps/picosat",
        commit = "4ee7aa1d1c645df8fa9daa07f2be17c6d03b35fc", # v965
        sha256 = "1be461d3659d4e3dc957a718ed295941c38dc822fd22a67f4cb5d180f0b6a7a3",
        build_file = str(Label("//tools:picosat.BUILD.bazel")),
    )
    github_archive(
        name = "pybind11", # BSD
        repository = "pybind/pybind11",
        commit = "v2.2.2",
        sha256 = "b639a2b2cbf1c467849660801c4665ffc1a4d0a9e153ae1996ed6f21c492064e",
        build_file = str(Label("//tools:pybind11.BUILD.bazel")),
    )
