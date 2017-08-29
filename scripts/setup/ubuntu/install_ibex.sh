#!/usr/bin/env bash
set -euo pipefail

die () {
    echo "$@" 1>&2
    exit 1
}

me="Ibex install script"

[[ $EUID -eq 0 ]] || die "$me must run as root. Please use sudo."

# Move to temporary directory.
cd `mktemp -d`

# Download ibex source 
curl -L https://github.com/ibex-team/ibex-lib/archive/ibex-2.5.1.tar.gz | tar xvz

# Download and apply patches
cd ibex-lib-ibex-2.5.1
curl -L https://raw.githubusercontent.com/dreal-deps/homebrew-ibex/master/clp_path.patch | patch -g 0 -f -p1 
curl -L https://raw.githubusercontent.com/dreal-deps/homebrew-ibex/master/use_std_min.patch | patch -g 0 -f -p1 
curl -L https://raw.githubusercontent.com/dreal-deps/homebrew-ibex/master/include_what_you_use.patch | patch -g 0 -f -p1
curl -L https://raw.githubusercontent.com/dreal-deps/homebrew-ibex/master/filib_log_interval.patch | patch -g 0 -f -p1

# Configure
./waf configure --enable-shared --with-optim --with-affine --interval-lib=filib --prefix=/usr

# Build
./waf build

# Install
sudo ./waf install
