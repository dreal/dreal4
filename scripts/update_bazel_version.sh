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

SCRIPT_PATH="$(dirname "$0")"
ROOT_PATH="${SCRIPT_PATH}"/..
VERSION=$1
DEB=bazel_${VERSION}-linux-x86_64.deb
URL=https://github.com/bazelbuild/bazel/releases/download/${VERSION}/${DEB}
wget "${URL}" -O "${DEB}"
SHA256=$(shasum -a 256 "${DEB}" | cut -d ' ' -f 1)
rm "${DEB}"

sed -i "s/BAZEL_VERSION=.*/BAZEL_VERSION=${VERSION}/g" $(find "${ROOT_PATH}"/setup -type f)
sed -i "s/BAZEL_SHA256=.*/BAZEL_SHA256=${SHA256}/g" $(find "${ROOT_PATH}"/setup -type f)
