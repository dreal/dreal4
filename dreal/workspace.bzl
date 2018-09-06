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
        commit = "v1.1.0",
        sha256 = "3dbcbfd8c07e25f5e0d662b194d3a7772ef214358c49ada23c044c4747ce8b19",
        build_file = str(Label("//tools:spdlog.BUILD.bazel")),
    )
    github_archive(
        name = "fmt",  # BSD2
        repository = "fmtlib/fmt",
        commit = "5.1.0",
        sha256 = "73d4cab4fa8a3482643d8703de4d9522d7a56981c938eca42d929106ff474b44",
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
