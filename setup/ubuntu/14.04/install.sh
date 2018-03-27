#!/bin/bash
set -euo pipefail

if [[ "${EUID}" -ne 0 ]]; then
  echo 'This script must be run as root' >&2
  exit 1
fi

add-apt-repository ppa:ubuntu-toolchain-r/test -y  # libstdc++6
add-apt-repository ppa:dreal/dreal -y  # For libibex-dev
apt update
apt install --no-install-recommends -y $(tr '\n' ' ' <<EOF
coinor-libclp-dev
libibex-dev
libnlopt-dev
libstdc++6
EOF
)

# Install bazel
DREAL_VERSION=4.18.03.1
DREAL_DEBNAME=dreal_${DREAL_VERSION}_amd64.deb
DREAL_URL=https://dl.bintray.com/dreal/dreal/${DREAL_DEBNAME}
DREAL_SHA256=0428d2de2364b724829b49de233fcac77f22496cccac7808df9523327c10dbf0
apt install --no-install-recommends wget -y
wget ${DREAL_URL}
if echo "${DREAL_SHA256}  ${DREAL_DEBNAME}" | sha256sum -c; then
    dpkg -i ${DREAL_DEBNAME}
    rm ${DREAL_DEBNAME}
else
    echo "SHA256 does not match ${DREAL_DEBNAME}:"
    echo "    expected: ${DREAL_SHA256}"
    echo "    actual  : `sha256sum ${DREAL_DEBNAME}`"
    exit 1
fi
