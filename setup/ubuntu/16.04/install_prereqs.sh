#!/bin/bash
set -euxo pipefail

if [[ "${EUID}" -ne 0 ]]; then
  echo 'This script must be run as root' >&2
  exit 1
fi

apt-get install -y --no-install-recommends software-properties-common || \
    ( (apt-get update || (sleep 30; apt-get update)) && \
	  apt-get install -y --no-install-recommends software-properties-common)
add-apt-repository ppa:dreal/dreal -y # For libibex-dev
apt-get update || (sleep 30; apt-get update)
apt-get install -y --no-install-recommends $(tr '\n' ' ' <<EOF
bison
coinor-libclp-dev
flex
g++
libgmp-dev
libibex-dev
libnlopt-dev
libpython3-dev
pkg-config
python-dev
zlib1g-dev
EOF
)

# Install bazel if needed
command_exists () {
    command -v $1 >/dev/null 2>&1;
}

if ! command_exists bazel; then
    BAZEL_VERSION=4.0.0
    BAZEL_DEBNAME=bazel_${BAZEL_VERSION}-linux-x86_64.deb
    BAZEL_URL=https://github.com/bazelbuild/bazel/releases/download/${BAZEL_VERSION}/${BAZEL_DEBNAME}
    BAZEL_SHA256=1779ce76ebf449e55dfdd1318355335179eb85609042dfe5c1b4b34683dfd4b5
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
fi
