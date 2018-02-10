import os
from sys import platform

WORKSPACE_PATH = os.path.dirname(os.path.abspath(__file__))
PROJECT_DIR = os.path.basename(WORKSPACE_PATH)
BAZEL_EXTERNAL = os.path.join(WORKSPACE_PATH, "bazel-%s" % PROJECT_DIR, "external")

if platform == "linux" or platform == "linux2":
  # linux
  PLATFORM_INCLUDE_PATH = "/usr/include"
  PLATFORM_SPECIFIC_SYSTEM_INCLUDES = [
    # Output of `clang-4.0 -std=c++11 -v -E -x c++ -`
    '/usr/include/c++/7',
    '/usr/include/x86_64-linux-gnu/c++/7',
    '/usr/include/c++/7/backward/',
    '/usr/include/clang/4.0.0/include',
    '/usr/local/include',
    '/usr/include/x86_64-linux-gnu',
    PLATFORM_INCLUDE_PATH,
  ]
  CLP_INCLUDES = [
    '%s/coin' % PLATFORM_INCLUDE_PATH,
  ]
  IBEX_INCLUDES = [
    '%s/ibex' % PLATFORM_INCLUDE_PATH,
    '%s/ibex/3rd' % PLATFORM_INCLUDE_PATH,
  ]
elif platform == "darwin":
  PLATFORM_INCLUDE_PATH = "/usr/local/include"
  PLATFORM_SPECIFIC_SYSTEM_INCLUDES = [
    # Output of `clang -std=c++11 -v -E -x c++ -`
    '/Applications/Xcode.app/Contents/Developer/Toolchains/XcodeDefault.xctoolchain/usr/include/c++/v1',
    PLATFORM_INCLUDE_PATH,
    '/Applications/Xcode.app/Contents/Developer/Toolchains/XcodeDefault.xctoolchain/usr/lib/clang/9.0.0/include',
    '/Applications/Xcode.app/Contents/Developer/Toolchains/XcodeDefault.xctoolchain/usr/include',
    '/usr/include',
  ]
  CLP_INCLUDES = [
    '%s/clp/coin' % PLATFORM_INCLUDE_PATH,
    '%s/coinutils/coin' % PLATFORM_INCLUDE_PATH,
  ]
  IBEX_INCLUDES = ["/usr/local/opt/ibex@2.6.5/include" + path for path in ["/", "/ibex", "/ibex/3rd"]]

SYSTEM_INCLUDES = IBEX_INCLUDES + CLP_INCLUDES + [
  # External packages
  '%s/spdlog/include' % BAZEL_EXTERNAL,
  '%s/fmt' % BAZEL_EXTERNAL,
  '%s/drake_symbolic' % BAZEL_EXTERNAL,
  '%s/ezoptionparser' % BAZEL_EXTERNAL,
  '%s/gtest/googletest/include' % BAZEL_EXTERNAL,
  '%s/picosat' % BAZEL_EXTERNAL,
] + PLATFORM_SPECIFIC_SYSTEM_INCLUDES

HOMEDIR = os.getenv('HOME')
BAZEL_EXTERNAL = os.path.join(WORKSPACE_PATH, 'bazel-%s' % PROJECT_DIR, "external")

def FlagsForFile( filename, **kwargs ):
  return {
    'flags': [ '-x', 'c++', '-std=c++14', '-Wall', '-Wextra', '-Werror',
               # everything in 'src' (including 'third-party')
               '-I%s' % WORKSPACE_PATH,
               '-I%s/bazel-genfiles' % WORKSPACE_PATH,
    ] + ['-isystem' + SYSTEM_INCLUDE for SYSTEM_INCLUDE in SYSTEM_INCLUDES],
  }
