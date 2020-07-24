def _impl(repository_ctx):
    if repository_ctx.os.name == "mac os x":
        repository_ctx.symlink(
            "/usr/local/opt/gmp/include/gmp.h",
            "include/gmp.h",
        )
        repository_ctx.symlink(
            "/usr/local/opt/gmp/include/gmpxx.h",
            "include/gmpxx.h",
        )
        repository_ctx.symlink(
            Label(
                "@dreal//third_party/org_gmplib:package-macos.BUILD.bazel",
            ),
            "BUILD.bazel",
        )
    elif repository_ctx.os.name == "linux":
        repository_ctx.symlink("/usr/include/x86_64-linux-gnu/gmp.h", "include/gmp.h")
        repository_ctx.symlink("/usr/include/gmpxx.h", "include/gmpxx.h")
        repository_ctx.symlink(
            Label(
                ("@dreal//third_party/org_gmplib:package-ubuntu.BUILD.bazel"),
            ),
            "BUILD.bazel",
        )
    else:
        fail("Operating system is NOT supported", attr = repository_ctx.os.name)

gmp_repository = repository_rule(
    configure = True,
    local = True,
    implementation = _impl,
)
