#!/bin/bash
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

# Install dReal
DREAL_VERSION=4.21.06.1
DREAL_DEBNAME=dreal_${DREAL_VERSION}_amd64.deb
DREAL_URL=https://github.com/dreal/dreal4/releases/download/${DREAL_VERSION}/${DREAL_DEBNAME}
DREAL_SHA256=c105906b92960fc675cd58751d735b3d465457822ceb6fabaf146c335d411f96
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
