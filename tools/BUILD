package(default_visibility = ["//visibility:private"])

sh_binary(
    name = "kcov",
    srcs = ["kcov.sh"],
)

sh_binary(
    name = "generate_version_header",
    srcs = [
        "generate_version_header.sh",
    ],
    visibility = ["//visibility:public"],
)

sh_binary(
    name = "generate_pkg_file_osx",
    srcs = [
        "generate_pkg_file_osx.sh",
    ],
    visibility = ["//visibility:public"],
)

sh_binary(
    name = "generate_pkg_file_ubuntu",
    srcs = [
        "generate_pkg_file_ubuntu.sh",
    ],
    visibility = ["//visibility:public"],
)

config_setting(
    name = "apple",
    constraint_values = ["@bazel_tools//platforms:osx"],
    visibility = ["//visibility:public"],
)

config_setting(
    name = "clang",
    constraint_values = ["@bazel_tools//tools/cpp:clang"],
    visibility = ["//visibility:public"],
)

config_setting(
    name = "debug",
    values = {"compilation_mode": "dbg"},
)

config_setting(
    name = "gcc",
    constraint_values = ["@bazel_tools//tools/cpp:gcc"],
    visibility = ["//visibility:public"],
)

config_setting(
    name = "linux",
    constraint_values = ["@bazel_tools//platforms:linux"],
    visibility = ["//visibility:public"],
)

config_setting(
    name = "PY2",
    flag_values = {"@bazel_tools//tools/python:python_version": "PY2"},
    visibility = ["//visibility:public"],
)

config_setting(
    name = "PY3",
    flag_values = {"@bazel_tools//tools/python:python_version": "PY3"},
    visibility = ["//visibility:public"],
)

licenses(["notice"])  # Apache 2.0

exports_files(["LICENSE"])
