#!/bin/bash
set -euxo pipefail

if [[ "${EUID}" -eq 0 ]]; then
  echo 'This script must NOT be run as root' >&2
  exit 1
fi

brew tap dreal-deps/ibex
brew update
brew install bazel pkg-config ibex@2.6.5 nlopt python@2
