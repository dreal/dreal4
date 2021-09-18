#!/usr/bin/env bash -vx
#
#  Copyright 2017 Toyota Research Institute
#
#  Licensed under the Apache License, Version 2.0 (the "License");
#  you may not use this file except in compliance with the License.
#  You may obtain a copy of the License at
#
#    http://www.apache.org/licenses/LICENSE-2.0
#
#  Unless required by applicable law or agreed to in writing, software
#  distributed under the License is distributed on an "AS IS" BASIS,
#  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
#  See the License for the specific language governing permissions and
#  limitations under the License.
#
me=$(python -c 'import os; print(os.path.realpath("'"$0"'"))')
WORKSPACE=$(dirname $(dirname "$me"))

# There must be ${WORKSPACE}/WORKSPACE.
if [ ! -f "${WORKSPACE}/WORKSPACE" ]; then
  echo "File not found: ${WORKSPACE}/WORKSPACE"
  exit 1
fi

# Just in case, don't collect data from cpplint tests.
if echo "$@" | grep -q _cpplint ; then
    "$@"
    exit $?
fi

kcov \
    --include-path=$WORKSPACE \
    $WORKSPACE/bazel-kcov \
    --replace-src-path=/proc/self/cwd:$WORKSPACE \
    --exclude-pattern=third_party,test \
    "$@"
