# Based on Drake's drake.bzl file,
# https://github.com/RobotLocomotion/drake/blob/master/tools/drake.bzl.

DREAL_VERSION = "4.19.04.2"

DREAL_PREFIX = "opt/dreal/%s" % DREAL_VERSION

PYTHON_VERSION_STRING = select({
    "@dreal//tools:PY3": "3",
    "@dreal//tools:PY2": "2.7",
})

PYTHON_PACKAGE_DIR = "lib/python" + PYTHON_VERSION_STRING + "/site-packages"

# The CXX_FLAGS will be enabled for all C++ rules in the project
# building with any compiler.
CXX_FLAGS = [
    "-Werror=all",
    "-Werror=attributes",
    "-Werror=deprecated",
    "-Werror=deprecated-declarations",
    "-Werror=ignored-qualifiers",
    "-Werror=old-style-cast",
    "-Werror=overloaded-virtual",
    "-Werror=shadow",
]

# The CLANG_FLAGS will be enabled for all C++ rules in the project when
# building with clang.
CLANG_FLAGS = CXX_FLAGS + [
    "-Werror=absolute-value",
    "-Werror=inconsistent-missing-override",
    "-Werror=non-virtual-dtor",
    "-Werror=return-stack-address",
    "-Werror=sign-compare",
]

# The GCC_FLAGS will be enabled for all C++ rules in the project when
# building with gcc.
GCC_FLAGS = CXX_FLAGS + [
    "-Werror=extra",
    "-Werror=logical-op",
    "-Werror=non-virtual-dtor",
    "-Werror=return-local-addr",
    "-Werror=unused-but-set-parameter",
]

# The GCC_CC_TEST_FLAGS will be enabled for all cc_test rules in the project
# when building with gcc.
GCC_CC_TEST_FLAGS = [
    "-Wno-unused-parameter",
]

def _platform_copts(rule_copts, cc_test = 0):
    """Returns both the rule_copts, and platform-specific copts.

    When cc_test=1, the GCC_CC_TEST_FLAGS will be added.  It should only be set
    to 1 from cc_test rules or rules that are boil down to cc_test rules.
    """
    extra_gcc_flags = []
    if cc_test:
        extra_gcc_flags = GCC_CC_TEST_FLAGS
    return select({
        "//tools:gcc": GCC_FLAGS + extra_gcc_flags + rule_copts,
        "//tools:clang": CLANG_FLAGS + rule_copts,
        "//tools:apple": CLANG_FLAGS + rule_copts,
        "//conditions:default": rule_copts,
    })

def _check_library_deps_blacklist(name, deps):
    """Report an error if a library should not use something from deps."""
    if not deps:
        return
    if type(deps) != "list":
        # We can't handle select() yet.
        return
    for dep in deps:
        if dep.endswith(":main"):
            fail("The cc_library '" + name + "' must not depend on a :main " +
                 "function from a cc_library; only cc_binary program should " +
                 "have a main function")

def dreal_cc_library(
        name,
        hdrs = None,
        srcs = None,
        deps = None,
        copts = [],
        **kwargs):
    """Creates a rule to declare a C++ library.
    """
    _check_library_deps_blacklist(name, deps)
    native.cc_library(
        name = name,
        hdrs = hdrs,
        srcs = srcs,
        deps = deps,
        copts = _platform_copts(copts),
        **kwargs
    )

def _make_search_paths(prefix, levels_to_root):
    return ",".join(
        [
            "-rpath,%s/%s" % (prefix, "/".join([".."] * search_level))
            for search_level in range(levels_to_root + 1)
        ],
    )

def dreal_pybind_library(
        name,
        py_srcs = [],
        py_deps = [],
        cc_srcs = [],
        cc_deps = []):
    """Creates a rule to declare a pybind library.

    Note that `cc_deps` should includes header-only dependencies.
    """
    cc_so_name = "_" + name + ".so"

    # The last +3 is for "lib/python*/site-packages".
    levels_to_root = native.package_name().count("/") + name.count("/") + 3
    dreal_cc_binary(
        name = cc_so_name,
        srcs = cc_srcs,
        linkshared = 1,
        linkstatic = 1,
        deps = cc_deps + [
            "//:dreal_shared_library",
            "@pybind11",
        ],
        copts = [
            "-fvisibility=hidden",
        ],
        linkopts = select({
            "@dreal//tools:linux": [
                "-Wl,%s" % (_make_search_paths("$$ORIGIN", levels_to_root),),
            ],
            "@//conditions:default": [],
        }),
    )
    native.py_library(
        name = name,
        srcs = py_srcs,
        data = [
            cc_so_name,
        ],
        deps = py_deps,
        srcs_version = "PY2AND3",
        visibility = ["//dreal:__subpackages__"],
    )

def dreal_cc_binary(
        name,
        hdrs = None,
        srcs = None,
        deps = None,
        copts = [],
        testonly = 0,
        add_test_rule = 0,
        test_rule_args = [],
        test_rule_size = None,
        **kwargs):
    """Creates a rule to declare a C++ binary.

    If you wish to create a smoke-test demonstrating that your binary runs
    without crashing, supply add_test_rule=1. Note that if you wish to do
    this, you should consider suppressing that urge, and instead writing real
    tests. The smoke-test will be named <name>_test. You may override cc_test
    defaults using test_rule_args=["-f", "--bar=42"] or test_rule_size="baz".
    """
    native.cc_binary(
        name = name,
        hdrs = hdrs,
        srcs = srcs,
        deps = deps,
        copts = _platform_copts(copts),
        testonly = testonly,
        **kwargs
    )

    if add_test_rule:
        dreal_cc_test(
            name = name + "_test",
            hdrs = hdrs,
            srcs = srcs,
            deps = deps,
            copts = copts,
            size = test_rule_size,
            testonly = testonly,
            args = test_rule_args,
            **kwargs
        )

def dreal_cc_test(
        name,
        size = None,
        srcs = None,
        copts = [],
        **kwargs):
    """Creates a rule to declare a C++ unit test.

    Note that for almost all cases, dreal_cc_googletest should be
    used, instead of this rule.

    By default, sets size="small" because that indicates a unit test.
    By default, sets name="test/${name}.cc" per Dreal's filename
    convention.

    """
    if size == None:
        size = "small"
    if srcs == None:
        srcs = ["test/%s.cc" % name]
    native.cc_test(
        name = name,
        size = size,
        srcs = srcs,
        copts = _platform_copts(copts, cc_test = 1),
        **kwargs
    )

def dreal_cc_googletest(
        name,
        deps = None,
        use_default_main = True,
        **kwargs):
    """Creates a rule to declare a C++ unit test using googletest.

    Always adds a deps= entry for googletest main
    (@com_google_googletest//:gtest_main).

    By default, sets size="small" because that indicates a unit test.
    By default, sets name="test/${name}.cc" per Dreal's filename convention.
    By default, sets use_default_main=True to use GTest's main, via
    @com_google_googletest//:gtest_main. Otherwise, it will depend on
    @com_google_googlegtest//:gtest.

    """
    if deps == None:
        deps = []
    if use_default_main:
        deps.append("@com_google_googletest//:gtest_main")
    else:
        deps.append("@com_google_googletest//:gtest")
    dreal_cc_test(
        name = name,
        deps = deps,
        **kwargs
    )

def smt2_test(
        name,
        tags = [],
        **kwargs):
    """Create smt2 test."""
    smt2 = name + ".smt2"
    expected = smt2 + ".expected"
    data_files = native.glob([
        smt2 + "*",
    ])
    native.py_test(
        name = name,
        args = [
            "$(location //dreal:dreal)",
            "$(location %s)" % smt2,
            "$(location %s)" % expected,
        ],
        tags = tags + ["smt2"],
        srcs = ["test.py"],
        data = [
            "//dreal:dreal",
        ] + data_files,
        main = "test.py",
        srcs_version = "PY2AND3",
        **kwargs
    )

def dr_test(
        name,
        args = [],
        **kwargs):
    """Create dr test."""
    dr = name + ".dr"
    expected = dr + ".expected"
    data_files = native.glob([
        dr + "*",
    ])
    native.py_test(
        name = name,
        args = [
            "$(location //dreal:dreal)",
            "$(location %s)" % dr,
            "$(location %s)" % expected,
        ] + args,
        tags = ["dr"],
        srcs = ["test.py"],
        data = [
            "//dreal:dreal",
        ] + data_files,
        main = "test.py",
        srcs_version = "PY2AND3",
        **kwargs
    )

# Generate a file with specified content
def _generate_file_impl(ctx):
    ctx.actions.write(output = ctx.outputs.out, content = ctx.attr.content)

dreal_generate_file = rule(
    attrs = {
        "content": attr.string(),
        "out": attr.output(mandatory = True),
    },
    output_to_genfiles = True,
    implementation = _generate_file_impl,
)
