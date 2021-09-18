#!/usr/bin/env bash
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

VERSION=$1
VERSION_ARRAY=( ${VERSION//./ } )
MAJOR=${VERSION_ARRAY[0]}
MINOR=${VERSION_ARRAY[1]}
REVISION=${VERSION_ARRAY[2]}

cat <<EOF
#pragma once
#define DREAL_VERSION_STRING  "${VERSION}"
#define DREAL_VERSION_FULL     ${VERSION}
#define DREAL_VERSION_MAJOR    ${MAJOR}
#define DREAL_VERSION_MINOR    ${MINOR}
#define DREAL_VERSION_REVISION ${REVISION}
EOF
