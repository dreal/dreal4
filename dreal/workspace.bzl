load("//third_party:com_github_robotlocomotion_drake/tools/workspace/github.bzl", "github_archive")
load("//third_party:com_github_robotlocomotion_drake/tools/workspace/pkg_config.bzl", "pkg_config_repository")

def dreal_workspace():
    pkg_config_repository(
        name = "ibex",  # LGPL3
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
        ],
    )
    pkg_config_repository(
        name = "python2",
        modname = "python2",
        pkg_config_paths = [
            "/usr/local/opt/python@2/lib/pkgconfig",
        ],
    )

    # We do not use this one, yet.
    pkg_config_repository(
        name = "python-3.5",
        modname = "python-3.5",
        pkg_config_paths = [
            "/usr/local/opt/python@3/lib/pkgconfig",
        ],
    )

    # We do not use this one, yet.
    pkg_config_repository(
        name = "python-3.6",
        modname = "python-3.6",
        pkg_config_paths = [
            "/usr/local/opt/python@3/lib/pkgconfig",
        ],
    )
    github_archive(
        name = "spdlog",  # MIT
        repository = "gabime/spdlog",
        commit = "v0.16.3",
        sha256 = "b88d7be261d9089c817fc8cee6c000d69f349b357828e4c7f66985bc5d5360b8",
        build_file = str(Label("//tools:spdlog.BUILD.bazel")),
    )
    github_archive(
        name = "fmt",  # BSD2
        repository = "fmtlib/fmt",
        commit = "4.1.0",
        sha256 = "46628a2f068d0e33c716be0ed9dcae4370242df135aed663a180b9fd8e36733d",
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
        commit = "v2.2.3",
        sha256 = "3a3b7b651afab1c5ba557f4c37d785a522b8030dfc765da26adc2ecd1de940ea",
        build_file = str(Label("//tools:pybind11.BUILD.bazel")),
    )
