#!/usr/bin/env bash

VERSION=$1
PREFIX=$2

cat <<EOF
prefix=/${PREFIX}
includedir=\${prefix}/include
libdir=\${prefix}/lib

Name: dReal
Description: SMT Solver for Nonlinear Theories
Version: ${VERSION}
Requires: ibex, nlopt
Libs: -L\${libdir} -ldreal
Cflags: -I\${includedir}
EOF
