def _impl(repository_ctx):
    if repository_ctx.os.name == "mac os x":
        if repository_ctx.path("/opt/homebrew/opt").exists:
            HOMEBREW_OPT = "/opt/homebrew/opt"
        else:
            HOMEBREW_OPT = "/usr/local/opt"

        repository_ctx.symlink(
            HOMEBREW_OPT + "/gmp/include/gmp.h",
            "include/gmp.h",
        )
        repository_ctx.symlink(
            HOMEBREW_OPT + "/gmp/include/gmpxx.h",
            "include/gmpxx.h",
        )
        repository_ctx.symlink(
            Label(
                "@dreal//tools:gmp_package_macos.BUILD.bazel",
            ),
            "BUILD.bazel",
        )
    elif repository_ctx.os.name == "linux":
        GMP_H_UBUNTU = "/usr/include/x86_64-linux-gnu/gmp.h"
        GMP_H_FEDORA = "/usr/include/gmp.h"
        if repository_ctx.path(GMP_H_UBUNTU).exists:
            repository_ctx.symlink(GMP_H_UBUNTU, "include/gmp.h")
        elif repository_ctx.path(GMP_H_FEDORA).exists:
            repository_ctx.symlink(GMP_H_FEDORA, "include/gmp.h")
        else:
            fail("Failed to locate gmp.h")
        repository_ctx.symlink("/usr/include/gmpxx.h", "include/gmpxx.h")
        repository_ctx.symlink(
            Label(
                "@dreal//tools:gmp_package_ubuntu.BUILD.bazel",
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
