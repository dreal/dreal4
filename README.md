dReal: An SMT Solver for Nonlinear Theories of Reals

[![License](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](https://opensource.org/licenses/Apache-2.0)
[![Build Status](https://travis-ci.org/dreal/dreal4.svg?branch=master)](https://travis-ci.org/dreal/dreal4)
[![Codecov Status](https://img.shields.io/codecov/c/github/dreal/dreal4.svg)](https://codecov.io/gh/dreal/dreal4)

Required Packages
=================

The following packages are required to build dReal:

 - C++14-compatible compiler
   - Ubuntu:
   [g++-7](https://gcc.gnu.org/gcc-7),
   [g++-6](https://gcc.gnu.org/gcc-6),
   [g++-5](https://gcc.gnu.org/gcc-5),
   [g++-4.9](https://gcc.gnu.org/gcc-4.9),
   [clang++-5.0](http://releases.llvm.org/5.0.0/tools/clang/docs),
   [clang++-4.0](http://releases.llvm.org/4.0.0/tools/clang/docs),
   [clang++-3.9](http://releases.llvm.org/3.9.0/tools/clang/docs)
   - macOS: [Apple clang++](https://developer.apple.com/library/content/documentation/CompilerTools/Conceptual/LLVMCompilerOverview/index.html)
 - [Bazel](https://bazel.build)
 - [Flex](https://www.gnu.org/software/flex) and [Bison](https://www.gnu.org/software/bison)
 - [Clp](https://projects.coin-or.org/Clp)
 - [IBEX](https://github.com/ibex-team/ibex-lib)

dReal is using the following external packages:

 - [Drake](http://drake.mit.edu)'s symbolic library - [BSD 3-Clause](https://raw.githubusercontent.com/RobotLocomotion/drake/master/LICENSE.TXT)
 - [Google Test](https://github.com/google/googletest) - [BSD 3-Clause](https://raw.githubusercontent.com/google/googletest/master/googletest/LICENSE)
 - [PicoSat SAT solver](http://fmv.jku.at/picosat) - [MIT](http://fmv.jku.at/picosat/LICENSE)
 - [ezOptionParser](http://ezoptionparser.sourceforge.net) - [MIT](https://raw.githubusercontent.com/dreal-deps/ezoptionparser/master/MIT-LICENSE)
 - [fmtlib](http://fmtlib.net/latest/index.html) - [BSD 2-Clause](https://raw.githubusercontent.com/fmtlib/fmt/master/LICENSE.rst)
 - [spdlog](https://github.com/gabime/spdlog) - [MIT](https://raw.githubusercontent.com/gabime/spdlog/master/LICENSE)

How to Install dReal
====================

macOS 10.12 (Sierra) / 10.13 (High Sierra):

```bash
brew install dreal/dreal/dreal
```

Ubuntu 14.04 LTS:
```bash
sudo add-apt-repository ppa:dreal/dreal -y
sudo add-apt-repository ppa:ubuntu-toolchain-r/test -y
sudo apt update
sudo apt install bison coinor-libclp-dev flex pkg-config libibex-dev libbz2-dev
sudo apt upgrade libstdc++6
wget https://dl.bintray.com/dreal/dreal/dreal_4.17.12.3_amd64.deb
dpkg -i dreal_4.17.12.3_amd64.deb
```

Ubuntu 16.04 LTS:
```bash
sudo apt install -y software-properties-common  # for add-apt-repository
sudo add-apt-repository ppa:dreal/dreal -y
sudo apt update
sudo apt install bison coinor-libclp-dev flex pkg-config libibex-dev libbz2-dev
wget https://dl.bintray.com/dreal/dreal/dreal_4.17.12.3_amd64.deb
dpkg -i dreal_4.17.12.3_amd64.deb
```

How to Build dReal
==================

Install Prerequsites
--------------------

macOS 10.12 (Sierra) / 10.13 (High Sierra):

```bash
brew install bazel pkg-config dreal-deps/ibex/ibex
```

Ubuntu 14.04 LTS / 16.04 LTS

```bash
sudo add-apt-repository ppa:dreal/dreal -y
sudo apt update
sudo apt install bison coinor-libclp-dev flex pkg-config libibex-dev libbz2-dev
```

Build and Test
--------------

```bash
bazel build //...
bazel test //...                     # Run all tests
./bazel-bin/dreal/dreal <smt2_file>  # Run .smt2 file
```

By default, it builds a release build. To build a debug-build, run
`bazel build //... -c dbg`. In macOS, pass `--config=apple_debug` to
allow lldb/gdb to show symbols.

In Ubuntu, it uses `clang-4.0` as a default compiler. To use other
compilers, pass `--compiler` option to bazel (for example `--compiler
gcc-5`). See
[tools/BUILD](https://github.com/dreal/dreal4/blob/master/tools/BUILD#L47-L75)
file for more information.

Build Debian Package
--------------------

Run `bazel build //:package_debian` and find `.deb` file in `bazel-bin` directory.


How to Build Compilation Database
-----------------------------------

To build a [Compilation
Database](https://clang.llvm.org/docs/JSONCompilationDatabase.html),
run:

```bash
curl -L https://github.com/grailbio/bazel-compilation-database/archive/0.2.tar.gz | tar -xz
bazel-compilation-database-0.2/generate.sh
```

How to Use dReal as a Library
=============================

After following the install steps,
[pkg-config](https://www.freedesktop.org/wiki/Software/pkg-config)
should work. That is, `pkg-config dreal --cflags` and `pkg-config
dreal --libs` should provide necessary information to use dReal.

We have also prepared the following example projects using dReal as a
library:
 - [dreal-cmake-example-project](https://github.com/dreal/dreal-cmake-example-project)
 - [dreal-bazel-example-project](https://github.com/dreal/dreal-bazel-example-project)
