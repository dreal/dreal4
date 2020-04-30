#!/bin/bash
set -euxo pipefail

if [[ "${EUID}" -eq 0 ]]; then
  echo 'This script must NOT be run as root' >&2
  exit 1
fi

brew tap dreal/dreal
brew update
brew cask install homebrew/cask-versions/adoptopenjdk8
brew install dreal --only-dependencies --build-from-source
