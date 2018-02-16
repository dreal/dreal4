# -*- python -*-
cc_library(
    name = "spdlog",
    hdrs = glob(["include/spdlog/**"]),
    defines = [
        "SPDLOG_FMT_EXTERNAL",
    ],
    includes = ["include"],
    linkopts = select({
        "@dreal//tools:linux": ["-pthread"],
        "@//conditions:default": [],
    }),
    visibility = ["//visibility:public"],
    deps = ["@fmt"],
)
