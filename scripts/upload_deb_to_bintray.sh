#!/usr/bin/env bash
ID=$1
PASSWORD=$2
VERSION=`cat VERSION`
DEB_FILENAME=dreal_${VERSION}_amd64.deb
BINTRAY_URL=https://api.bintray.com/content/dreal/dreal/dreal

set -e

# BUILD
bazel build //:package_debian --compiler=gcc-4.9

# Renaming: Until https://github.com/bazelbuild/bazel/issues/3652 is fixed.
mv bazel-bin/dreal__amd64.deb dreal_${VERSION}_amd64.deb

if [ -e ${DEB_FILENAME} ]
then
  # Upload Files
  curl -T ${DEB_FILENAME} -u${ID}:${PASSWORD} ${BINTRAY_URL}/${VERSION}/${DEB_FILENAME}
  # Publish version
  curl -X POST -u${ID}:${PASSWORD} ${BINTRAY_URL}/${VERSION}/publish
  # Remove the bottle
  rm -v ${DEB_FILENAME}
else 
  echo "File not found: ${DEB_FILENAME}"
fi

