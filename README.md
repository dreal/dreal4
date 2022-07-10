dReal: An SMT Solver for Nonlinear Theories of Reals

[![License](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](https://opensource.org/licenses/Apache-2.0)
[![Build Status](https://travis-ci.org/dreal/dreal4.svg?branch=master)](https://travis-ci.org/dreal/dreal4)
[![codecov](https://codecov.io/gh/dreal/dreal4/branch/master/graph/badge.svg)](https://codecov.io/gh/dreal/dreal4)

How to Install
==============

macOS 12 / 11 / 10.15:

```bash
/usr/bin/curl -fsSL https://raw.githubusercontent.com/dreal/dreal4/master/setup/mac/install.sh | bash
dreal
```

Ubuntu 22.04 / 20.04 / 18.04:

```bash
# 22.04
sudo apt-get install curl
curl -fsSL https://raw.githubusercontent.com/dreal/dreal4/master/setup/ubuntu/22.04/install.sh | sudo bash

# 20.04
sudo apt-get install curl
curl -fsSL https://raw.githubusercontent.com/dreal/dreal4/master/setup/ubuntu/20.04/install.sh | sudo bash

# 18.04
sudo apt-get install curl
curl -fsSL https://raw.githubusercontent.com/dreal/dreal4/master/setup/ubuntu/18.04/install.sh | sudo bash

# Test the installation.
DREAL_VERSION=4.21.06.2
/opt/dreal/${DREAL_VERSION}/bin/dreal
```


Python Binding
==============

[![Open In Google Colab](https://colab.research.google.com/assets/colab-badge.svg)](https://colab.research.google.com/github/dreal/dreal4/blob/master/notebooks/dreal4-python3.ipynb)

Some of the functionality of dReal is accessible via Python3. To
install the binding, run the following:
```bash
pip3 install dreal
```

Note that you still need to install dReal prerequisites such as IBEX
and CLP in your system. Please follow [the
instructions](https://github.com/dreal/dreal4#install-prerequsites).


To test the Python binding, run `python3` in a terminal and type the
followings:

```python
from dreal import *

x = Variable("x")
y = Variable("y")
z = Variable("z")

f_sat = And(0 <= x, x <= 10,
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

More examples are available at
[dreal4/dreal/test/python](https://github.com/dreal/dreal4/tree/master/dreal/test/python).


Docker
======

We provide a [Docker image of
dReal4](https://hub.docker.com/r/dreal/dreal4/tags/) which is based on
Ubuntu 18.04. Try the following to test it:

```bash
docker pull dreal/dreal4
docker run --rm dreal/dreal4 dreal -h  # Run "dreal -h"
```


How to Build
============

Install Prerequisites
--------------------

macOS 12 / 11 / 10.15:

```bash
git clone https://github.com/dreal/dreal4 && cd dreal4
./setup/mac/install_prereqs.sh
```

Ubuntu 22.04 / 20.04 / 18.04

```bash
git clone https://github.com/dreal/dreal4 && cd dreal4
sudo ./setup/ubuntu/`lsb_release -r -s`/install_prereqs.sh
```

The `install_prereqs.sh` installs the following packages: 
[bazel](https://bazel.build), 
[bison](https://www.gnu.org/software/bison), 
[coinor-clp](https://projects.coin-or.org/Clp), 
[flex](https://www.gnu.org/software/flex), 
[gmp](https://gmplib.org),
[ibex](https://github.com/ibex-team/ibex-lib), 
[nlopt](http://nlopt.readthedocs.io), 
[python](https://www.python.org).


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
set up `CC` environment variable. For example, `CC=gcc-7 bazel build
//...`.

In CI, we test that dReal can be built using the following compilers:
 - Ubuntu:
   [clang-9](https://releases.llvm.org/9.0.0/tools/clang/docs/),
   [clang-10](https://releases.llvm.org/10.0.0/tools/clang/docs/),
   [clang-11](https://releases.llvm.org/11.0.0/tools/clang/docs/),
   [clang-12](https://releases.llvm.org/12.0.0/tools/clang/docs/),
   [clang-13](https://releases.llvm.org/13.0.0/tools/clang/docs/),
   [clang-14](https://releases.llvm.org/14.0.0/tools/clang/docs/),
   [gcc-7](https://gcc.gnu.org/gcc-7),
   [gcc-9](https://gcc.gnu.org/gcc-9),
   [gcc-10](https://gcc.gnu.org/gcc-10),
   [gcc-11](https://gcc.gnu.org/gcc-11)
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
bazel build //:compdb
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

macOS 12 / 11 / 10.15:

```bash
export PKG_CONFIG_PATH=/usr/local/opt/ibex@2.7.4/share/pkgconfig:${PKG_CONFIG_PATH}
```

Ubuntu 22.04 / 20.04 / 18.04:

```bash
export PKG_CONFIG_PATH=/opt/dreal/4.21.06.2/lib/pkgconfig:/opt/libibex/2.7.4/share/pkgconfig:${PKG_CONFIG_PATH}
```

Then, `pkg-config dreal --cflags` and `pkg-config dreal --libs` should
provide necessary information to use dReal. Note that setting up
`PKG_CONFIG_PATH` is necessary to avoid possible conflicts (i.e. with
`ibex` formula in Mac).

Command-line Options
====================

```
-h, -help, --help, --usage   Display usage instructions.

-j, --jobs ARG               Number of jobs.

-v, --version                Print version number of dReal.

--debug-parsing              Debug parsing

--debug-scanning             Debug scanning/lexing

--forall-polytope            Use polytope contractor in forall contractor.

--format ARG                 File format. Any one of these (default = auto):
                             smt2, dr, auto (use file extension)

--in                         Read from standard input. Uses smt2 by default.

--local-optimization         Use local optimization algorithm for exist-forall
                             problems.

--model, --produce-models    Produce models if delta-sat

--nlopt-ftol-abs ARG         [NLopt] Absolute tolerance on function value
                             (default = 1e-06)

--nlopt-ftol-rel ARG         [NLopt] Relative tolerance on function value
                             (default = 1e-06)

--nlopt-maxeval ARG          [NLopt] Number of maximum function evaluations
                             (default = 100)

--nlopt-maxtime ARG          [NLopt] Maximum optimization time (in second)
                             (default = 0.01 sec)

--polytope                   Use polytope contractor.

--precision ARG              Precision (default = 0.001)

--random-seed ARG            Set a seed for the random number generator.

--sat-default-phase ARG      Set default initial phase for SAT solver.
                               0 = false
                               1 = true
                               2 = Jeroslow-Wang (default)
                               3 = random initial phase

--smtlib2-compliant          Strictly follow the smtlib2 standard.

--verbose ARG                Verbosity level. Either one of these (default =
                             error):
                             trace, debug, info, warning, error, critical, off

--worklist-fixpoint          Use worklist fixpoint algorithm in ICP.
```
