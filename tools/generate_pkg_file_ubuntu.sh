#!/usr/bin/env bash

read VERSION < $1

cat <<EOF
prefix=/usr
includedir=\${prefix}/include
libdir=\${prefix}/lib

Name: dReal
Description: SMT Solver for Nonlinear Theories
Version: ${VERSION}
Requires: ibex, nlopt
Libs: -L\${libdir} -ldreal
Cflags: -I\${includedir}
EOF
