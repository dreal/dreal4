#!/usr/bin/env bash
set -euo pipefail

SCRIPT_PATH=$(dirname "$0")
ROOT_PATH="${SCRIPT_PATH}/.."

# Check pyenv is installed.
command -v pyenv >/dev/null 2>&1 || (echo "pyenv is not installed."; exit 1)

# Check macOS / Ubuntu version to maintain backward compatibility
if [[ "$OSTYPE" == "linux-gnu" ]]; then
    SUPPORTED_UBUNTU_VERSION=16.04
    CURRENT_UBUNTU_VERSION=$(grep "DISTRIB_RELEASE" /etc/lsb-release | cut -d "=" -f 2)
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
PYTHON_VERSIONS="3.6.11"                    # End Of Life: 2021-12-23
PYTHON_VERSIONS="${PYTHON_VERSIONS} 3.7.9"  # End Of Life: 2023-06-27
PYTHON_VERSIONS="${PYTHON_VERSIONS} 3.8.6"  # End Of Life: 2024-10
PYTHON_VERSIONS="${PYTHON_VERSIONS} 3.9.0"  # End Of Life: 2025-10

for PYTHON_VERSION in ${PYTHON_VERSIONS}
do
    echo "${PYTHON_VERSION}"
    pyenv install --skip-existing "${PYTHON_VERSION}"
    pyenv local "${PYTHON_VERSION}"
    rm -rf "${ROOT_PATH}/build"
    python3 -m pip install --user --upgrade setuptools wheel pip

    echo "Build wheel for ${PYTHON_VERSION}"
    cd "${ROOT_PATH}" && python3 setup.py bdist_wheel
done

echo "To upload, run twine upload dist/*"
