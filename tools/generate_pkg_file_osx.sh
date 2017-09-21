#!/usr/bin/env bash

read VERSION < $1

if [ -z ${HOMEBREW_CELLAR+x} ]; then
    echo "cellar=`brew --cellar`"
else
    # We're inside of homebrew installation where this variable is set.
    echo "cellar=${HOMEBREW_CELLAR}"
fi

cat <<EOF
libdir=\${cellar}/dreal/${VERSION}/lib
includedir=\${cellar}/dreal/${VERSION}/include

Name: dReal
Description: SMT Solver for Nonlinear Theories
Version: ${VERSION}
Requires: ibex
Libs: -L\${libdir} -ldreal
Cflags: -I\${includedir} -I\${includedir}/dreal
EOF
