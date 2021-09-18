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

display_usage() {
    echo "usage: $0 <new_version_string>"
}

if [ $# -ne 1 ]
then
    display_usage
    exit 1
fi

SCRIPT_PATH="`dirname \"$0\"`"
ROOT_PATH="${SCRIPT_PATH}/.."
OLD_VERSION=`grep "DREAL_VERSION = " "${ROOT_PATH}/tools/dreal.bzl" | cut -d '"' -f 2`
NEW_VERSION=$1

echo -n "Updating ${OLD_VERSION} => ${NEW_VERSION}... "
sed -i "s/${OLD_VERSION}/${NEW_VERSION}/g" \
    "${ROOT_PATH}/README.md" \
    "${ROOT_PATH}/setup.py" \
    "${ROOT_PATH}/setup/ubuntu/18.04/install.sh" \
    "${ROOT_PATH}/setup/ubuntu/20.04/install.sh" \
    "${ROOT_PATH}/tools/dreal.bzl" \
    "${ROOT_PATH}/dreal/__init__.py"
echo "Done"

DREAL_DEBNAME=dreal_${NEW_VERSION}_amd64.deb
DREAL_URL=https://github.com/dreal/dreal4/releases/download/${NEW_VERSION}/${DREAL_DEBNAME}

wget ${DREAL_URL} -O ${DREAL_DEBNAME}
SHA256=`shasum -a 256 ${DREAL_DEBNAME} | cut -d ' ' -f 1`
rm ${DREAL_DEBNAME}
sed -i "s/DREAL_SHA256=.*/DREAL_SHA256=${SHA256}/g" `find "${ROOT_PATH}/setup" -type f`
echo -n "Updated dReal SHA in setup scripts."
