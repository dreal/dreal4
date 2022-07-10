#!/usr/bin/env bash
#
#  Copyright 2022 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

# Install dReal
DREAL_VERSION=4.21.06.2
DREAL_DEBNAME=dreal_${DREAL_VERSION}_amd64.deb
DREAL_URL=https://github.com/dreal/dreal4/releases/download/${DREAL_VERSION}/${DREAL_DEBNAME}
DREAL_SHA256=c1798357bd967bf84b06fdaf7e962e102ff6703b3dee546fdc02862a1ecc09f1
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
