dReal: An SMT Solver for Nonlinear Theories of Reals

[![License](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](https://opensource.org/licenses/Apache-2.0)
[![Build Status](https://travis-ci.org/dreal/dreal4.svg?branch=master)](https://travis-ci.org/dreal/dreal4)
[![Codecov Status](https://img.shields.io/codecov/c/github/dreal/dreal4.svg)](https://codecov.io/gh/dreal/dreal4)

Required Packages
=================

The following packages are required to build dReal:

 - C++14-compatible compilers (i.e.
   [g++-7](https://gcc.gnu.org/gcc-7),
   [g++-6](https://gcc.gnu.org/gcc-6),
   [g++-5](https://gcc.gnu.org/gcc-5),
   [g++-4.9](https://gcc.gnu.org/gcc-4.9),
   [clang++-4.0](http://releases.llvm.org/4.0.0/tools/clang/docs),
   [clang++-3.9](http://releases.llvm.org/3.9.0/tools/clang/docs),
   [Apple clang++](https://developer.apple.com/library/content/documentation/CompilerTools/Conceptual/LLVMCompilerOverview/index.html))
 - [Bazel](https://bazel.build)
 - [Flex](https://www.gnu.org/software/flex)
   and [Bison](https://www.gnu.org/software/bison)
 - [Autoconf](http://www.gnu.org/software/autoconf/autoconf.html),
   [Automake](https://www.gnu.org/software/automake/),
   and [libtool](https://www.gnu.org/software/libtool/)

dReal is using the following external libraries:

 - [Clp](https://projects.coin-or.org/Clp) - [EPL 1.0](https://opensource.org/licenses/eclipse-1.0)
 - [Drake](http://drake.mit.edu) - [BSD 3-Clause](https://raw.githubusercontent.com/RobotLocomotion/drake/master/LICENSE.TXT)
 - [IBEX](https://github.com/ibex-team/ibex-lib) - [LGPL3](https://raw.githubusercontent.com/ibex-team/ibex-lib/master/LICENSE)
 - [PicoSat SAT solver](http://fmv.jku.at/picosat) - [MIT](http://fmv.jku.at/picosat/LICENSE)
 - [ezOptionParser](http://ezoptionparser.sourceforge.net) - [MIT](https://raw.githubusercontent.com/dreal-deps/ezoptionparser/master/MIT-LICENSE)
 - [spdlog](https://github.com/gabime/spdlog) - [MIT](https://raw.githubusercontent.com/gabime/spdlog/master/LICENSE)
 - [Google Test](https://github.com/google/googletest) - [BSD 3-Clause](https://raw.githubusercontent.com/google/googletest/master/googletest/LICENSE)

How to Build
============

Install Prerequsites
--------------------

macOS:

```bash
brew install autoconf automake bazel libtool pkg-config dreal-deps/ibex/ibex
```

Ubuntu

```bash
sudo add-apt-repository ppa:dreal/dreal -y
sudo apt update
sudo apt install autoconf automake bison coinor-libclp-dev flex libtool pkg-config libibex-dev
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


How to Build Compilation Database
-----------------------------------

To build a [Compilation
Database](https://clang.llvm.org/docs/JSONCompilationDatabase.html),
run:

```bash
pip install protobuf    # required to run only once
./scripts/generate_compile_commands.sh
```
