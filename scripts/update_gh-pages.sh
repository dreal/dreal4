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
set -euo pipefail

# Build doxygen
doxygen

# Move the contents to a temp dir
TMP_DIR=$(mktemp -d)
mv doxygen_cxx/html/* "${TMP_DIR}"
rm -rf doxygen_cxx

# Remove the existing 'gh-pages' branch 
git branch -D gh-pages

# Create a brand-new branch gh-pages and copy the contents
git checkout --orphan gh-pages
git rm -rf .
mv "${TMP_DIR}"/* .
rm -rf "${TMP_DIR}"

# Add/Commit/Push
git add -- *.css *.html *.js *.png search
git commit -m "Update doxygen $(date)"
git push blessed HEAD:gh-pages -f

# Checkout back to master
git checkout master
