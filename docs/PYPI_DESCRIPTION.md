dReal4: SMT Solver for Nonlinear Theories of Reals
==================================================

Please visit https://github.com/dreal/dreal4.

Installation
------------

    pip install dreal
    # or
    uv add dreal

Prebuilt wheels are self-contained: IBEX, CLP, NLopt, GMP and the other
native dependencies are bundled, so nothing else needs to be installed.
They are available for:

 - Linux (manylinux_2_28, i.e. glibc >= 2.28) on x86_64 and aarch64
 - macOS on Apple Silicon (arm64) and Intel (x86_64)
 - CPython 3.12, 3.13 and 3.14

Example
-------

```python
from dreal import *

x = Variable("x")
y = Variable("y")
f = And(0 <= x, x <= 10, 0 <= y, y <= 10, sin(x) + cos(y) == 0)
print(CheckSatisfiability(f, 0.001))
```

Build from Source
-----------------

If no wheel matches your platform, `pip` builds dReal from the source
distribution. That requires Bazel and dReal's native prerequisites. See
https://github.com/dreal/dreal4#install-prerequsites, or
`scripts/wheels/install_deps.sh` in the source tree.
