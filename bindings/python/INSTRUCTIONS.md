# Install required packages
```bash
python2 -m pip install --upgrade twine
python2 -m pip install --user --upgrade setuptools wheel
python3 -m pip install --user --upgrade setuptools wheel
```

# To build
```bash
python2 setup.py sdist bdist_wheel
python3 setup.py sdist bdist_wheel
```

# To upload
```bash
twine upload --repository testpypi dist/*  # To testpypi
twine upload dist/*                        # To pypi
```bash

# To install
```bash
python2 -m pip install --index-url https://test.pypi.org/simple/ dreal  # from testpypi
python2 -m pip install dreal                                            # from pypi
```
