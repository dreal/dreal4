#!/bin/bash
set -euo pipefail

if [[ "${EUID}" -ne 0 ]]; then
  echo 'This script must be run as root' >&2
  exit 1
fi

apt-get update;
apt-get install -y software-properties-common
add-apt-repository ppa:dreal/dreal -y  # For libibex-dev
apt-get update

# Install dReal
DREAL_VERSION=4.20.08.1
DREAL_DEBNAME=dreal_${DREAL_VERSION}_amd64.deb
DREAL_URL=https://dl.bintray.com/dreal/dreal/${DREAL_DEBNAME}
DREAL_SHA256=2892fcc2029219d3b8c0c1d02171bdc31a2c1ed6e3825e79b5b8346840f15f11
apt-get install --no-install-recommends wget -y
wget "${DREAL_URL}"
if echo "${DREAL_SHA256}  ${DREAL_DEBNAME}" | sha256sum -c; then
    dpkg --install --skip-same-version ./"${DREAL_DEBNAME}" || apt-get -f install -y
    rm "${DREAL_DEBNAME}"
else
    echo "SHA256 does not match ${DREAL_DEBNAME}:"
    echo "    expected: ${DREAL_SHA256}"
    echo "    actual  : $(sha256sum "${DREAL_DEBNAME}")"
    exit 1
fi
