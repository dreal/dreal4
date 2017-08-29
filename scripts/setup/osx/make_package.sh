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

# Download/uncompress drake-symbolic
curl -L https://github.com/dreal-deps/drake-symbolic/archive/master.tar.gz | tar xvz

# Copy drake-symbolic headers to usr/include
mkdir usr/include/symbolic
cp drake-symbolic-master/symbolic/symbolic_expression.h \
   drake-symbolic-master/symbolic/symbolic_expression_visitor.h \
   drake-symbolic-master/symbolic/symbolic_formula.h \
   drake-symbolic-master/symbolic/symbolic_formula_visitor.h \
   drake-symbolic-master/symbolic/symbolic_variable.h \
   drake-symbolic-master/symbolic/symbolic_variables.h \
   drake-symbolic-master/symbolic/symbolic_environment.h \
   drake-symbolic-master/symbolic/hash.h \
   usr/include/symbolic


# Change install name
chmod +w usr/lib/libdreal.so
install_name_tool -id @rpath/libdreal.so usr/lib/libdreal.so
chmod -w usr/lib/libdreal.so

tar cvfz dreal.tar.gz usr

echo "Package created at `pwd`/dreal.tar.gz"
