#!/usr/bin/env bash

set -euo pipefail

if [[ $EUID -eq 0 ]]; then
  echo "This script must NOT be run as root" >&2
  exit 1
fi

bazel build //:package
PACKAGE_FILE=`pwd`/bazel-bin/package.tar.gz

# Move to temporary directory.
cd `mktemp -d`
tar xvfz $PACKAGE_FILE  # unpack dreal package

# Change install name
chmod +w usr/lib/libdreal.so
install_name_tool -id @rpath/libdreal.so usr/lib/libdreal.so
chmod -w usr/lib/libdreal.so

tar cvfz dreal.tar.gz usr

echo "Package created at `pwd`/dreal.tar.gz"
