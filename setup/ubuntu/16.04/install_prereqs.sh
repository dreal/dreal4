#!/bin/bash
set -euo pipefail

if [[ "${EUID}" -ne 0 ]]; then
  echo 'This script must be run as root' >&2
  exit 1
fi

add-apt-repository ppa:dreal/dreal -y  # For libibex-dev
apt update;
apt install -y --no-install-recommends $(tr '\n' ' ' <<EOF
bison
flex
libpython2.7-dev
openjdk-8-jdk
pkg-config
python-dev
zlib1g-dev
coinor-libclp-dev
libibex-dev
libnlopt-dev
EOF
)
      
# Install bazel
BAZEL_VERSION=0.12.0
BAZEL_DEBNAME=bazel_${BAZEL_VERSION}-linux-x86_64.deb
BAZEL_URL=https://github.com/bazelbuild/bazel/releases/download/${BAZEL_VERSION}/${BAZEL_DEBNAME}
BAZEL_SHA256=f3df344b16a40d4233a7606cce38869d4df3bb35296ac2f4e18838566ae3cb48
apt install -y --no-install-recommends wget
wget ${BAZEL_URL}
if echo "${BAZEL_SHA256}  ${BAZEL_DEBNAME}" | sha256sum -c; then
    dpkg -i ${BAZEL_DEBNAME}
    rm ${BAZEL_DEBNAME}
else
    echo "SHA256 does not match ${BAZEL_DEBNAME}:"
    echo "    expected: ${BAZEL_SHA256}"
    echo "    actual  : `sha256sum ${BAZEL_DEBNAME}`"
    exit 1
fi
