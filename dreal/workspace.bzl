load("//third_party:com_github_robotlocomotion_drake/tools/workspace/github.bzl", "github_archive")
load("//third_party:com_github_robotlocomotion_drake/tools/workspace/pkg_config.bzl", "pkg_config_repository")

def dreal_workspace():
    pkg_config_repository(
        name = "ibex",  # LGPL3
        modname = "ibex",
        pkg_config_paths = [
            # macOS
            "/usr/local/opt/ibex@2.7.2/share/pkgconfig",
            "/usr/local/opt/ibex@2.6.5/share/pkgconfig",  # TODO(soonho): Remove this
            "/usr/local/opt/clp/lib/pkgconfig",  # dep of ibex, EPL
            "/usr/local/opt/coinutils/lib/pkgconfig",  # dep of clp, EPL
            # Linux
            "/opt/libibex/2.7.2/share/pkgconfig",
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

    pkg_config_repository(
        name = "python3",
        modname = "python3",
        pkg_config_paths = [
            "/usr/local/opt/python@3/lib/pkgconfig",
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

    # We do not use this one, yet.
    pkg_config_repository(
        name = "python-3.7",
        modname = "python-3.7",
        pkg_config_paths = [
            "/usr/local/opt/python@3/lib/pkgconfig",
        ],
    )

    github_archive(
        name = "spdlog",  # MIT
        repository = "gabime/spdlog",
        commit = "v1.2.1",
        sha256 = "867a4b7cedf9805e6f76d3ca41889679054f7e5a3b67722fe6d0eae41852a767",
        build_file = str(Label("//tools:spdlog.BUILD.bazel")),
    )

    github_archive(
        name = "fmt",  # BSD2
        repository = "fmtlib/fmt",
        commit = "5.2.1",
        sha256 = "3c812a18e9f72a88631ab4732a97ce9ef5bcbefb3235e9fd465f059ba204359b",
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
        commit = "v2.2.4",
        sha256 = "b69e83658513215b8d1443544d0549b7d231b9f201f6fc787a2b2218b408181e",
        build_file = str(Label("//tools:pybind11.BUILD.bazel")),
    )

    github_archive(
        name = "com_google_absl",  # BSD
        repository = "abseil/abseil-cpp",
        commit = "13327debebc5c2d1d4991b69fe50450e340e50e4",  # 20181127
        sha256 = "39cbe974e02601c76fbb1619084064908be18bf33b0372c68f4ca05112c8332e",
    )
