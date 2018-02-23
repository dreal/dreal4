#!/usr/bin/env bash

set -e

VERSION=$1

cat <<EOF
prefix=HOMEBREW_PREFIX/opt/dreal
libdir=\${prefix}/lib
includedir=\${prefix}/include

Name: dReal
Description: SMT Solver for Nonlinear Theories
Version: ${VERSION}
Requires: ibex, nlopt
Libs: -L\${libdir} -ldreal
Cflags: -I\${includedir}
EOF
