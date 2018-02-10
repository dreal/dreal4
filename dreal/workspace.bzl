# -*- python -*-
load("//tools:github.bzl", "github_archive")
load("//tools:third_party/com_github_robotlocomotion_drake/tools/workspace/pkg_config.bzl", "pkg_config_repository")

def dreal_workspace():
    pkg_config_repository(
        name = "ibex", # LGPL3
        modname = "ibex",
        pkg_config_paths = [
            "/usr/local/opt/ibex@2.6.5/share/pkgconfig",
            "/usr/local/opt/clp/lib/pkgconfig",  # dep of ibex
            "/usr/local/opt/coinutils/lib/pkgconfig",  # dep of clp
        ],
    )
    pkg_config_repository(
        name = "nlopt",  # LGPL2 + MIT
        modname = "nlopt",
        pkg_config_paths = [
            "/usr/local/opt/nlopt/lib/pkgconfig",
        ]
    )
    github_archive(
        name = "drake_symbolic", # BSD
        repository = "dreal-deps/drake-symbolic",
        commit = "907695dd6d3ec0a4b69faa0df18b03a13b631e0f",
        sha256 = "d2a4343e2b334752c3a7deecf2a5a4da83fc773a7a3f516c44c62d8823714667",
    )
    github_archive(
        name = "spdlog", # MIT
        repository = "gabime/spdlog",
        commit = "1e4f14c78965c4bdb6c4b2917ad06d21ab87e21d",
        sha256 = "056597b3dc00b3de3eee8cc93f0a7ef277abf89330049f705508b3ccefeaeab4",
        build_file = str(Label("//tools:spdlog.BUILD")),
    )
    github_archive(
        name = "fmt", # BSD2
        repository = "fmtlib/fmt",
        commit = "d16c4d20f88c738d79ecec7c355584f7e161e03e",
        sha256 = "dc1830521fcf37ed380473ebd9d73c2bd7824c8eb120567ea900ead24d1196c9",
        build_file = str(Label("//tools:fmt.BUILD")),
    )
    github_archive(
        name = "picosat", # MIT
        repository = "dreal-deps/picosat",
        commit = "b17ad98a29ac64b1e62182e40a01bd616b129418",
        sha256 = "b47f084ae6ac75c7ce921a1930bfa3d2de7c89ff4911d8107ecb1e90d87abdf1",
        build_file = str(Label("//tools:picosat.BUILD")),
    )
