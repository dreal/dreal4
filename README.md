dReal: An SMT Solver for Nonlinear Theories of Reals

[![License](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](https://opensource.org/licenses/Apache-2.0)
[![Build Status](https://travis-ci.org/dreal/dreal4.svg?branch=master)](https://travis-ci.org/dreal/dreal4)
[![codecov](https://codecov.io/gh/dreal/dreal4/branch/master/graph/badge.svg)](https://codecov.io/gh/dreal/dreal4)

How to Install
==============

macOS 10.13 / 10.12 / 10.11:

```bash
/usr/bin/curl -fsSL https://raw.githubusercontent.com/dreal/dreal4/master/setup/mac/install.sh | bash
dreal
```

Ubuntu 18.04 / 16.04:

```bash
# 18.04
sudo apt-get install curl
curl -fsSL https://raw.githubusercontent.com/dreal/dreal4/master/setup/ubuntu/18.04/install.sh | sudo bash

# 16.04
sudo apt-get install curl
curl -fsSL https://raw.githubusercontent.com/dreal/dreal4/master/setup/ubuntu/16.04/install.sh | sudo bash

# Test the installation.
DREAL_VERSION=4.18.08.1
/opt/dreal/${DREAL_VERSION}/bin/dreal
```


Python Binding
==============

Some of the functionality of dReal is accessible through Python2. On
Ubuntu 18.04 / 16.04, you need to set up the `PYTHONPATH` environment
variable. On macOS, you do not need this step.

```bash
# Only on Ubuntu 18.04 / 16.04:
export PYTHONPATH=/opt/dreal/4.18.08.1/lib/python2.7/site-packages:${PYTHONPATH}
```

To test it, run `python2` in a terminal and type the followings:

```python
from dreal.symbolic import Variable, logical_and, sin, cos
from dreal.api import CheckSatisfiability, Minimize

x = Variable("x")
y = Variable("y")
z = Variable("z")

f_sat = logical_and(0 <= x, x <= 10,
                    0 <= y, y <= 10,
                    0 <= z, z <= 10,
                    sin(x) + cos(y) == z)

result = CheckSatisfiability(f_sat, 0.001)
print(result)
```

The last `print` statement should give:

```
x : [1.247234518484574339, 1.247580203674002686]
y : [8.929064928123818135, 8.929756298502674383]
z : [0.06815055407334302817, 0.06858905276351445757]
```

Python3 support is experimental for now. Please read [this
comment](https://github.com/dreal/dreal4/issues/69#issuecomment-377085510)
for instructions.


Docker
======

We provide a [Docker image of
dReal4](https://hub.docker.com/r/dreal/dreal4/tags/) which is based on
Ubuntu 18.04. Try the following to test it:

```bash
docker pull dreal/dreal4
docker run --rm dreal/dreal4 dreal --version  # Run "dreal --version"
```


How to Build
============

Install Prerequsites
--------------------

macOS 10.13 / 10.12 / 10.11:

```bash
git clone https://github.com/dreal/dreal4 && cd dreal4
./setup/mac/install_prereqs.sh
```

Ubuntu 18.04 / 16.04

```bash
git clone https://github.com/dreal/dreal4 && cd dreal4
sudo ./setup/ubuntu/`lsb_release -r -s`/install_prereqs.sh
```

The `install_prereqs.sh` installs the following packages: [bazel](https://bazel.build), [bison](https://www.gnu.org/software/bison), [coinor-clp](https://projects.coin-or.org/Clp), [flex](https://www.gnu.org/software/flex), [ibex](https://github.com/ibex-team/ibex-lib), [nlopt](http://nlopt.readthedocs.io), [python2.7](https://www.python.org/downloads/release/python-2714/).


Build and Test
--------------

```bash
bazel build //...
bazel test //...                     # Run all tests
./bazel-bin/dreal/dreal <smt2_file>  # Run .smt2 file
```

By default, it builds a release build. To build a debug-build, run
`bazel build //... -c dbg`. In macOS, pass `--apple_generate_dsym` to
allow lldb/gdb to show symbols.

Bazel uses the system default compiler. To use a specific compiler,
set up `CC` environment variable. For example, `CC=gcc-8.0 bazel build
//...`.

In CI, we test that dReal can be built using the following compilers:
 - Ubuntu:
   [gcc-8](https://gcc.gnu.org/gcc-8),
   [gcc-7](https://gcc.gnu.org/gcc-7),
   [gcc-6](https://gcc.gnu.org/gcc-6),
   [gcc-5](https://gcc.gnu.org/gcc-5),
   [clang-6.0](http://releases.llvm.org/6.0.0/tools/clang/docs),
   [clang-5.0](http://releases.llvm.org/5.0.0/tools/clang/docs),
   [clang-4.0](http://releases.llvm.org/4.0.0/tools/clang/docs),
   [clang-3.9](http://releases.llvm.org/3.9.0/tools/clang/docs)
 - macOS: [Apple clang](https://developer.apple.com/library/content/documentation/CompilerTools/Conceptual/LLVMCompilerOverview/index.html)


C++ Documentation
-----------------

Please check https://dreal.github.io/dreal4.


Build Debian Package
--------------------

Run `bazel build //:package_debian` and find `.deb` file in `bazel-bin` directory.


How to Build Compilation Database
-----------------------------------

To build a [Compilation
Database](https://clang.llvm.org/docs/JSONCompilationDatabase.html),
run:

```bash
./third_party/com_github_grailbio_bazel-compilation-database/generate.sh
```


How to Use dReal as a Library
=============================

We have prepared the following example projects using dReal as a
library:

 - [dreal-cmake-example-project](https://github.com/dreal/dreal-cmake-example-project)
 - [dreal-bazel-example-project](https://github.com/dreal/dreal-bazel-example-project)

If you want to use
[pkg-config](https://www.freedesktop.org/wiki/Software/pkg-config),
you need to set up `PKG_CONFIG_PATH` as follows:

macOS 10.13 / 10.12 / 10.11:

```bash
export PKG_CONFIG_PATH=/usr/local/opt/ibex@2.6.5/share/pkgconfig:${PKG_CONFIG_PATH}
```

Ubuntu 18.04 / 16.04:

```bash
export PKG_CONFIG_PATH=/opt/dreal/4.18.08.1/lib/pkgconfig:/opt/libibex/2.6.5/share/pkgconfig:${PKG_CONFIG_PATH}
```

Then, `pkg-config dreal --cflags` and `pkg-config dreal --libs` should
provide necessary information to use dReal. Note that setting up
`PKG_CONFIG_PATH` is necessary to avoid possible conflicts (i.e. with
`ibex` formula in Mac).


