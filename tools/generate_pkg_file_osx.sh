#!/usr/bin/env bash

read VERSION < $1

cat <<EOF
libdir=/usr/local/Cellar/dreal/${VERSION}/lib
includedir=/usr/local/Cellar/dreal/${VERSION}/include

Name: dReal
Description: SMT Solver for Nonlinear Theories
Version: ${VERSION}
Requires: ibex
Libs: -L\${libdir} -ldreal
Cflags: -I\${includedir} -I\${includedir}/dreal
EOF
