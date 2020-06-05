#!/bin/bash
set -euo pipefail

if [[ "${EUID}" -ne 0 ]]; then
  echo 'This script must be run as root' >&2
  exit 1
fi
apt-get update
apt-get install -y --no-install-recommends software-properties-common
add-apt-repository ppa:dreal/dreal -y  # For libibex-dev
apt-get update
apt-get install -y --no-install-recommends $(tr '\n' ' ' <<EOF
bison
coinor-libclp-dev
g++
libfl-dev
libibex-dev
libnlopt-cxx-dev
pkg-config
zlib1g-dev
EOF
)

if [[ ! -e /usr/bin/python ]]; then
    apt-get install -y --no-install-recommends python-is-python3
fi

dpkg -s python-is-python3 >/dev/null 2>&1 && apt-get install -y --no-install-recommends \
						     libpython3-dev \
						     python3-distutils \
						     python3-minimal

dpkg -s python-is-python2 >/dev/null 2>&1 && apt-get install -y --no-install-recommends \
						     libpython2.7-dev \
						     python2.7-minimal

# Install bazel
BAZEL_VERSION=3.1.0
BAZEL_DEBNAME=bazel_${BAZEL_VERSION}-linux-x86_64.deb
BAZEL_URL=https://github.com/bazelbuild/bazel/releases/download/${BAZEL_VERSION}/${BAZEL_DEBNAME}
BAZEL_SHA256=8fb2fe222c479a24e4d089f30bf30aea36fc8bfa117d81cce1ad9adf1f743bf0
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
