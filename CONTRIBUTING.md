Contributing to dReal
=====================

We want to make contributing to this project as easy and transparent
as possible.

Pull Requests
-------------

We welcome your pull requests. Please check the followings before you
open a PR.

1. **{COORDINATE}** Before writing code, please contact us so that we
   can discuss the high-level ideas and implementation-details
   together.

1. **{CODING STYLE}** We follow [Google's C++ Style
   Guide](https://google.github.io/styleguide/cppguide.html) and
   [PEP8 - Style Guide for Python Code
   ](https://www.python.org/dev/peps/pep-0008/). We have code linters
   integrated in testing. Please make sure that you code do not
   generate warnings.

1. **{TEST COVERAGE}** Please write enough test cases for your
   changes. We have [kcov]() setup which you can check the
   code-coverage locally.

1. **{PR SIZE}** Please make sure that your PR is small enough to
   review. If your PR includes more than *750 lines of changes*,
   please consider split it into multiple PRs. `git diff --stat`
   should give you a good summary of the size of your PR.

1. **{BUILD}** Please make sure that your changes compile. In ubuntu,
   build your code with *both* of gcc and clang:
   
   ```bash
   bazel build //... --compiler=g++-5
   bazel build //... --compiler=clang-4.0
   ...
   ```

1. **{TEST}** Please make sure that all the regression tests still
   pass with your changes. Run

   ```bash
   bazel test //...
   ```

1. **{ASAN}** Please make sure that [clang
   sanitizers](https://clang.llvm.org/docs/AddressSanitizer.html) do
   not detect any problems. Run

   ```bash
   bazel test //... --config=asan
   ```
1. **{CODE REVIEW}** We are using
   [reviewable.io](https://reviewable.io) for code review. If you are
   new to it, please read [nice
   tips](http://drake.mit.edu/reviewable.html) of using it.

Issues
------

We use [GitHub issues](https://github.com/dreal/dreal4/issues/new) to
track public bugs. Please ensure your description is clear and has
sufficient instructions to be able to reproduce the issue. Please
consider adding the following information to your issue:

 - dReal version: Output from `dreal`.
 - OS version: Output from `sw_vers` (macOS), `lsb_release -a` (Ubuntu).
 - Compiler: g++/llvm-clang/apple-clang + version.
 - SMT2 file(s) or code snippet which demonstrates the problem.
 - Bazel version: Output from `bazel version`.
 - Build commit: Output from `git log -n 1 --oneline`.

License
-------

By contributing to dReal, you agree that your contributions will be licensed
under the LICENSE file in the root directory of this source tree.
