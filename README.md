dReal: An SMT Solver for Nonlinear Theories of Reals

[![Build Status](https://travis-ci.org/dreal/dreal3-apache2.svg?branch=master)](https://travis-ci.org/dreal/dreal3-apache2)

Required Packages
=================

The following packages are required to build dReal:

 - C++14-compatible compilers
   (i.e. [g++-6](https://gcc.gnu.org/gcc-6),
   [g++-5](https://gcc.gnu.org/gcc-5),
   [g++-4.9](https://gcc.gnu.org/gcc-4.9),
   [clang++-3.9](http://releases.llvm.org/3.9.0/tools/clang/docs),
   [Apple clang++](https://developer.apple.com/library/content/documentation/CompilerTools/Conceptual/LLVMCompilerOverview/index.html))
 - [Bazel](https://bazel.build)
 - [Flex](https://www.gnu.org/software/flex)
   and [Bison](https://www.gnu.org/software/bison)
 - [Autoconf](http://www.gnu.org/software/autoconf/autoconf.html),
   [Automake](https://www.gnu.org/software/automake/),
   and [libtool](https://www.gnu.org/software/libtool/)

dReal is using the following external libraries:
 - [Clp](https://projects.coin-or.org/Clp)
 - [Drake](http://drake.mit.edu)
 - [IBEX](https://github.com/ibex-team/ibex-lib)
 - [PicoSat SAT solver](http://fmv.jku.at/picosat)
 - [ezOptionParser](http://ezoptionparser.sourceforge.net)
 - [spdlog](https://github.com/gabime/spdlog)
 - [Google Test](https://github.com/google/googletest)

How to Build
============

Install Prerequsites
--------------------

macOS:

```bash
brew install autoconf automake bazel libtool pkg-config
brew install dreal-deps/ibex/ibex  # install ibex+clp
```

Ubuntu

```bash
sudo add-apt-repository ppa:dreal/dreal -y
sudo apt update
sudo apt install autoconf automake bison coinor-libclp-dev \
                 flex libtool pkg-config libibex-dev
```

Build
-----

To build:

```bash
bazel build //...
bazel test //...
./bazel-bin/dreal/dreal <smt2_file>
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
./generate_compile_commands.sh
```
