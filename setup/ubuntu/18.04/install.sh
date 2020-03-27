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
DREAL_VERSION=4.20.03.4
DREAL_DEBNAME=dreal_${DREAL_VERSION}_amd64.deb
DREAL_URL=https://dl.bintray.com/dreal/dreal/${DREAL_DEBNAME}
DREAL_SHA256=40f121efe343abee984c3c01b8ed04d4d773b071f0646eb03eecd09d3c9104e5
apt-get install --no-install-recommends wget -y
wget "${DREAL_URL}"
if echo "${DREAL_SHA256}  ${DREAL_DEBNAME}" | sha256sum -c; then
    apt-get install -y ./"${DREAL_DEBNAME}"
    rm "${DREAL_DEBNAME}"
else
    echo "SHA256 does not match ${DREAL_DEBNAME}:"
    echo "    expected: ${DREAL_SHA256}"
    echo "    actual  : $(sha256sum "${DREAL_DEBNAME}")"
    exit 1
fi
