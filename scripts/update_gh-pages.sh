#!/usr/bin/env bash
set -euo pipefail

# Build doxygen
doxygen

# Move the contents to a temp dir
TMP_DIR=`mktemp -d`
mv doxygen_cxx/html/* ${TMP_DIR}
rm -rf doxygen_cxx

# Remove the existing 'gh-pages' branch 
git branch -D gh-pages

# Create a brand-new branch gh-pages and copy the contents
git checkout --orphan gh-pages
git rm -rf .
mv ${TMP_DIR}/* .
rm -rf ${TMP_DIR}

# Add/Commit/Push
git add *
git commit -m "Update doxygen `date`"
git push blessed HEAD:gh-pages -f

# Checkout back to master
git checkout master
