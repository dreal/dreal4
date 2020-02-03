#!/usr/bin/env bash
set -euo pipefail

display_usage() {
    echo "usage: $0 <new_version_string>"
}

if [ $# -ne 1 ]
then
    display_usage
    exit 1
fi

SCRIPT_PATH="$(dirname \""$0"\")"
ROOT_PATH="${SCRIPT_PATH}/.."
VERSION=$1
DEB=bazel_${VERSION}-linux-x86_64.deb
URL=https://github.com/bazelbuild/bazel/releases/download/${VERSION}/${DEB}
wget "${URL}" -O "${DEB}"
SHA256=$(shasum -a 256 "${DEB}" | cut -d ' ' -f 1)
rm "${DEB}"

sed -i "s/BAZEL_VERSION=.*/BAZEL_VERSION=${VERSION}/g" "$(find "${ROOT_PATH}"/setup -type f)"
sed -i "s/BAZEL_SHA256=.*/BAZEL_SHA256=${SHA256}/g" "$(find "${ROOT_PATH}"/setup -type f)"
