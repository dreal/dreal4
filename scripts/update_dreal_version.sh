#!/usr/bin/env bash
set -euo pipefail

OLD_VERSION=$1
NEW_VERSION=$2
sed -i "s/${OLD_VERSION}/${NEW_VERSION}/g" README.md bindings/python/setup.py setup/ubuntu/*/install.sh tools/dreal.bzl

DREAL_DEBNAME=dreal_${NEW_VERSION}_amd64.deb
DREAL_URL=https://dl.bintray.com/dreal/dreal/${DREAL_DEBNAME}

wget ${DREAL_URL} -O ${DREAL_DEBNAME}
SHA256=`shasum -a 256 ${DREAL_DEBNAME} | cut -d ' ' -f 1`
rm ${DREAL_DEBNAME}
sed -i "s/DREAL_SHA256=.*/DREAL_SHA256=${SHA256}/g" `find setup -type f`
