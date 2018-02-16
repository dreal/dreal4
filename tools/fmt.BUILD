# -*- python -*-

package(
    default_visibility = ["//visibility:public"],
)

cc_library(
    name = "fmt",
    hdrs = glob([
        "fmt/*.cc",
        "fmt/*.h",
    ]),
    defines = ["FMT_HEADER_ONLY=1"],
    includes = ["."],
)
