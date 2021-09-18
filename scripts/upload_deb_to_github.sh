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

set -euf -o pipefail

display_usage() {
    echo "usage: $0 <GITHUB_TOKEN>"
}

if [ "$(lsb_release -r -s)" != "18.04" ]
then
    echo "Please run this script on Ubuntu 18.04"
    exit 1
fi

if [ $# -ne 1 ]
then
    display_usage
    exit 1
fi

GITHUB_RELEASE="${HOME}/go/bin/github-release"

if [ ! -f "${GITHUB_RELEASE}" ]
then
    go get github.com/github-release/github-release
fi

if [ ! -f "${GITHUB_RELEASE}" ]
then
    echo "Failed to install github-release via go get".
    echo "Please visit https://github.com/github-release/github-release and follow the installation instructions."
    exit 1
fi

# BUILD
CC=gcc-7 bazel build //:package_debian

GH_TOKEN=$1
WORKSPACE=$(bazel info workspace)
VERSION=$(grep "DREAL_VERSION_FULL" "${WORKSPACE}"/bazel-bin/dreal/version.h | tr -s " " | cut -d ' ' -f 3-)
DEB_FILENAME=dreal_${VERSION}_amd64.deb
DEB_FILEPATH=${WORKSPACE}/bazel-bin/${DEB_FILENAME}

# Check if there exists the release.
"${GITHUB_RELEASE}" info -u dreal -r dreal4 -t "${VERSION}" || exit_code=$?
if [ ${exit_code} -ne 0 ]
then
    # Create a new release.
    "${GITHUB_RELEASE}" release \
			-u dreal \
			-r dreal4 \
			-s "${GH_TOKEN}" \
			--tag "${VERSION}" \
			--pre-release \
			--draft \
			-n "${VERSION}"
fi

if [ -f "${DEB_FILEPATH}" ]
then
    # Upload Files
    echo "Uploading ${DEB_FILEPATH} / ${VERSION}..."
    "${GITHUB_RELEASE}" upload \
    			-u dreal \
			-r dreal4 \
			-s "${GH_TOKEN}" \
			--tag "${VERSION}" \
			--file "${DEB_FILEPATH}" \
			-n "${DEB_FILENAME}"
    echo "Uploading ${DEB_FILEPATH} / ${VERSION}... DONE."
else
    echo "File not found: ${DEB_FILEPATH}"
fi
