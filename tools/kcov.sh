#!/bin/bash -vx


me=$(python -c 'import os; print(os.path.realpath("'"$0"'"))')
WORKSPACE=$(dirname $(dirname "$me"))

# Just in case, don't collect data from cpplint tests.
if echo "$@" | grep -q _cpplint ; then
    "$@"
    exit $?
fi

# If travis job id is set, upload it to coveralls.
if [ -z ${TRAVIS_JOB_ID+x} ]; then
    kcov \
        --include-path=$WORKSPACE \
        --exclude-pattern=thirdParty,externals \
        $WORKSPACE/bazel-kcov \
        --replace-src-path=/proc/self/cwd:$WORKSPACE \
        "$@"
else
    kcov \
        --include-path=$WORKSPACE \
        --exclude-pattern=thirdParty,externals \
        $WORKSPACE/bazel-kcov \
        --coveralls-id=${TRAVIS_JOB_ID} \
        --replace-src-path=/proc/self/cwd:$WORKSPACE \
        "$@"
fi
