#!/usr/bin/env bash
set -euo pipefail

SCRIPT_PATH="`dirname \"$0\"`"
ROOT_PATH="${SCRIPT_PATH}/.."

# Check pyenv is installed.
command -v pyenv >/dev/null 2>&1 || (echo "pyenv is not installed."; exit 1)

# Check macOS / Ubuntu version to maintain backward compatibility
if [[ "$OSTYPE" == "linux-gnu" ]]; then
    SUPPORTED_UBUNTU_VERSION=16.04
    CURRENT_UBUNTU_VERSION=$(cat /etc/lsb-release | grep "DISTRIB_RELEASE" | cut -d "=" -f 2)
    if [[ "${CURRENT_UBUNTU_VERSION}" != "${SUPPORTED_UBUNTU_VERSION}" ]]; then
	echo "Please use Ubuntu-${SUPPORTED_UBUNTU_VERSION}."
	exit 1
    fi
elif [[ "$OSTYPE" == "darwin"* ]]; then
    SUPPORTED_MACOS_VERSION=10.13.6
    if [[ $(sw_vers -productVersion) != "${SUPPORTED_MACOS_VERSION}" ]]; then
	echo "Please use macOS-${SUPPORTED_MACOS_VERSION}."
	exit 1
    fi
else
    echo "OSTYPE should be either linux-gnu or darwin, but it is ${OSTYPE}".
fi

# Install active python releases.
PYTHON_35_VERSION=3.5.9   # End Of Life: 2020-09-13
PYTHON_36_VERSION=3.6.10  # End Of Life: 2021-12-23
PYTHON_37_VERSION=3.7.7   # End Of Life: 2023-06-27
PYTHON_38_VERSION=3.8.2   # End Of Life: 2024-10
PYTHON_VERSIONS="${PYTHON_35_VERSION} ${PYTHON_36_VERSION} ${PYTHON_37_VERSION} ${PYTHON_38_VERSION}"
pyenv install --skip-existing ${PYTHON_35_VERSION}
pyenv install --skip-existing ${PYTHON_36_VERSION}
pyenv install --skip-existing ${PYTHON_37_VERSION}
pyenv install --skip-existing ${PYTHON_38_VERSION}


for PYTHON_VERSION in ${PYTHON_VERSIONS}
do
    echo "${PYTHON_VERSION}"
    pyenv local "${PYTHON_VERSION}"
    rm -rf "${ROOT_PATH}/build"
    python3 -m pip install --user --upgrade setuptools wheel pip

    echo "Build wheel for ${PYTHON_VERSION}"
    cd "${ROOT_PATH}" && python3 setup.py bdist_wheel
done

echo "To upload, run twine upload dist/*"
