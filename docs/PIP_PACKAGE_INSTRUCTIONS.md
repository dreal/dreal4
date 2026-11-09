# Building wheels

Release wheels are built by [cibuildwheel](https://cibuildwheel.pypa.io)
in `.github/workflows/wheels.yml`. Publishing a GitHub release uploads them
(and the sdist) to PyPI via trusted publishing.

Each wheel is self-contained: `scripts/wheels/install_deps.sh` builds
CoinUtils, CLP, NLopt and IBEX from pinned sources, Bazel builds
`_dreal_py.so` / `libdreal_.so`, and auditwheel (Linux) or delocate (macOS)
copies the shared libraries into the wheel. Each wheel is then tested in a
clean environment with `scripts/wheels/smoke_test.py`. The configuration
lives under `[tool.cibuildwheel]` in `pyproject.toml`.

# To build locally

Linux wheels (needs Docker or Podman):
```bash
uvx cibuildwheel --platform linux                        # Docker
CIBW_CONTAINER_ENGINE=podman uvx cibuildwheel --platform linux
```

macOS wheels (needs Homebrew; installs Bazel and builds prerequisites in
`~/dreal-deps`):
```bash
MACOSX_DEPLOYMENT_TARGET=14.0 uvx cibuildwheel --platform macos
```

Wheels are written to `wheelhouse/`.

A development build against prerequisites already installed on your system
(e.g., via `setup/ubuntu/<version>/install_prereqs.sh`):
```bash
pip install .
```

# To upload manually
```bash
twine upload --repository testpypi wheelhouse/* dist/*.tar.gz  # To testpypi
twine upload wheelhouse/* dist/*.tar.gz                        # To pypi
```

# To install
```bash
python3 -m pip install --index-url https://test.pypi.org/simple/ dreal  # from testpypi
python3 -m pip install dreal                                            # from pypi
```
