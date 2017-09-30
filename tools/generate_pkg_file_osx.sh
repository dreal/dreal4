#!/usr/bin/env bash

set -e

read VERSION < $1

if type "brew" > /dev/null; then
    # brew is available, so use it.
    echo "cellar=`brew --cellar`"
else
    # brew is not available. We need to replace this later.
    echo "cellar=HOMEBREW_CELLAR"
fi

cat <<EOF
libdir=\${cellar}/dreal/${VERSION}/lib
includedir=\${cellar}/dreal/${VERSION}/include

Name: dReal
Description: SMT Solver for Nonlinear Theories
Version: ${VERSION}
Requires: ibex
Libs: -L\${libdir} -ldreal
Cflags: -I\${includedir}
EOF
