# -*- python -*-
cc_library(
    name = "spdlog",
    srcs = glob(
        [
            "include/**/*.h",
        ],
        exclude = [
            "include/spdlog/spdlog.h",
        ],
    ),
    hdrs = ["include/spdlog/spdlog.h"],
    defines = [
        "SPDLOG_FMT_EXTERNAL",
    ],
    includes = [
        "include",
    ],
    linkopts = select({
        "@dreal//tools:linux": ["-pthread"],
        "@//conditions:default": [],
    }),
    linkstatic = 1,
    visibility = ["//visibility:public"],
    deps = ["@fmt"],
)
