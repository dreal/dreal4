#!/usr/bin/env bash
#
#  Copyright 2017 Toyota Research Institute
#
#  Licensed under the Apache License, Version 2.0 (the "License");
#  you may not use this file except in compliance with the License.
#  You may obtain a copy of the License at
#
#    http://www.apache.org/licenses/LICENSE-2.0
#
#  Unless required by applicable law or agreed to in writing, software
#  distributed under the License is distributed on an "AS IS" BASIS,
#  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
#  See the License for the specific language governing permissions and
#  limitations under the License.
#
set -euo pipefail

SCRIPT_PATH=$(dirname "$0")
ROOT_PATH="${SCRIPT_PATH}/.."

# Check pyenv is installed.
command -v pyenv >/dev/null 2>&1 || (echo "pyenv is not installed."; exit 1)

# Check macOS / Ubuntu version to maintain backward compatibility
if [[ "$OSTYPE" == "linux-gnu" ]]; then
    SUPPORTED_UBUNTU_VERSION=18.04
    CURRENT_UBUNTU_VERSION=$(grep "DISTRIB_RELEASE" /etc/lsb-release | cut -d "=" -f 2)
    if [[ "${CURRENT_UBUNTU_VERSION}" != "${SUPPORTED_UBUNTU_VERSION}" ]]; then
	echo "Please use Ubuntu-${SUPPORTED_UBUNTU_VERSION}."
	exit 1
    fi
elif [[ "$OSTYPE" == "darwin"* ]]; then
    SUPPORTED_MACOS_VERSION=11.6.4
    if [[ $(sw_vers -productVersion) != "${SUPPORTED_MACOS_VERSION}" ]]; then
	echo "Please use macOS-${SUPPORTED_MACOS_VERSION}."
	exit 1
    fi
else
    echo "OSTYPE should be either linux-gnu or darwin, but it is ${OSTYPE}".
fi

# Install active python releases.
PYTHON_VERSIONS="3.7.12"                     # End Of Life: 2023-06-27
PYTHON_VERSIONS="${PYTHON_VERSIONS} 3.8.12"  # End Of Life: 2024-10
PYTHON_VERSIONS="${PYTHON_VERSIONS} 3.9.10"  # End Of Life: 2025-10
PYTHON_VERSIONS="${PYTHON_VERSIONS} 3.10.2"  # End Of Life: 2026-10

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
