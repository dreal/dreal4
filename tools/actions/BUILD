# -*- python -*-
# This file contains rules for Bazel; see https://bazel.io/ .

py_binary(
    name = "generate_compile_command",
    srcs = [
        "generate_compile_command.py",
    ],
    deps = [
        "//tools/third_party/com_github_bazelbuild_bazel:extra_actions_proto_py",
    ],
)

action_listener(
    name = "generate_compile_commands_listener",
    extra_actions = [":generate_compile_commands_action"],
    mnemonics = [
        "CppCompile",
    ],
    visibility = ["//visibility:public"],
)

extra_action(
    name = "generate_compile_commands_action",
    cmd = "$(location :generate_compile_command) $(EXTRA_ACTION_FILE)" +
          " $(output $(ACTION_ID)_compile_command)",
    out_templates = [
        "$(ACTION_ID)_compile_command",
    ],
    tools = [
        ":generate_compile_command",
    ],
)
