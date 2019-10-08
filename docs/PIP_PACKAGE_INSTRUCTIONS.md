# Install required packages
```bash
python3 -m pip install --upgrade twine
python3 -m pip install --user --upgrade setuptools wheel pip
```

# Extra
```bash
python3 -m pip install keyring keyrings.alt 
```

# To build
```bash
python3 setup.py sdist bdist_wheel
```

# To upload
```bash
twine upload --repository testpypi dist/*  # To testpypi
twine upload dist/*                        # To pypi
```

# To install
```bash
python3 -m pip install --index-url https://test.pypi.org/simple/ dreal  # from testpypi
python3 -m pip install dreal                                            # from pypi
```
