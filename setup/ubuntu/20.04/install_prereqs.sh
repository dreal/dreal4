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
set -euxo pipefail

if [[ "${EUID}" -ne 0 ]]; then
  echo 'This script must be run as root' >&2
  exit 1
fi

apt-get install -y --no-install-recommends software-properties-common || \
    ( (apt-get update || (sleep 30; apt-get update)) && \
	  apt-get install -y --no-install-recommends software-properties-common)
add-apt-repository ppa:dreal/dreal --no-update -y  # For libibex-dev
apt-get update || (sleep 30; apt-get update)
apt-get install -y --no-install-recommends $(tr '\n' ' ' <<EOF
bison
coinor-libclp-dev
g++
libfl-dev
libgmp-dev
libibex-dev
libnlopt-cxx-dev
libpython3-dev
pkg-config
python3-distutils
python3-minimal
zlib1g-dev
EOF
)

# Install bazel
BAZEL_VERSION=5.0.0
BAZEL_DEBNAME=bazel_${BAZEL_VERSION}-linux-x86_64.deb
BAZEL_URL=https://github.com/bazelbuild/bazel/releases/download/${BAZEL_VERSION}/${BAZEL_DEBNAME}
BAZEL_SHA256=e3361645ccd731abc424bb3a322d8e6f513b7258f5ca11ff04d6067aff5d09b1
apt-get install -y --no-install-recommends wget
wget "${BAZEL_URL}"
if echo "${BAZEL_SHA256}  ${BAZEL_DEBNAME}" | sha256sum -c; then
    dpkg --install --skip-same-version ./"${BAZEL_DEBNAME}" || apt-get -f install -y
    rm "${BAZEL_DEBNAME}"
else
    echo "SHA256 does not match ${BAZEL_DEBNAME}:"
    echo "    expected: ${BAZEL_SHA256}"
    echo "    actual  : $(sha256sum "${BAZEL_DEBNAME}")"
    exit 1
fi
