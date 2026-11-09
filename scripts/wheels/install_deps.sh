#!/usr/bin/env bash
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
# Builds dReal's native prerequisites (CoinUtils, CLP, NLopt, IBEX) from
# pinned, checksum-verified sources into ${DREAL_DEPS_PREFIX} and installs
# Bazel. Used by cibuildwheel (see `[tool.cibuildwheel]` in pyproject.toml)
# to produce self-contained wheels: auditwheel / delocate later copy these
# shared libraries into the wheel, so end users need none of them.
#
# Supported hosts:
#   - manylinux_2_28 containers (AlmaLinux 8, dnf), x86_64 / aarch64
#   - macOS with Homebrew, x86_64 / arm64
#
# Environment variables:
#   DREAL_DEPS_PREFIX  Install prefix (default: /opt/dreal-deps).
#   WAF_PYTHON         Python 3 used to run IBEX's waf (default: python3).
#   MACOSX_DEPLOYMENT_TARGET  Honored on macOS.
set -euxo pipefail

PREFIX="${DREAL_DEPS_PREFIX:-/opt/dreal-deps}"
JOBS="$(getconf _NPROCESSORS_ONLN 2>/dev/null || sysctl -n hw.ncpu)"
OS="$(uname -s)"
ARCH="$(uname -m)"

COINUTILS_VERSION=2.11.12
COINUTILS_SHA256=eef1785d78639b228ae2de26b334129fe6a7d399c4ac6f8fc5bb9054ba00de64
CLP_VERSION=1.17.10
CLP_SHA256=0d79ece896cdaa4a3855c37f1c28e6c26285f74d45f635046ca0b6d68a509885
NLOPT_VERSION=2.10.0
NLOPT_SHA256=506f83a9e778ad4f204446e99509cb2bdf5539de8beccc260a014bd560237be1
# Same IBEX as the dreal PPA / Homebrew `ibex@2.7.4` formula.
IBEX_VERSION=2.7.4_13
IBEX_SHA256=d5524eb7e8f1edf6fe7867bea617bf450ad05e2c2eb5e8048a8532619e0ec0e1
BAZEL_VERSION=7.0.0
WAF_PYTHON="${WAF_PYTHON:-python3}"

# --- System packages and Bazel --------------------------------------------
if [[ "${OS}" == "Linux" ]]; then
  dnf install -y gmp-devel bison flex pkgconfig zlib-devel patch
  case "${ARCH}" in
    x86_64)
      BAZEL_PLATFORM=linux-x86_64
      BAZEL_SHA256=8b24f70542f9736e0ccbf9cb3335cb9f049b5a6787f1e5997ed1da80b9bbd46e ;;
    aarch64)
      BAZEL_PLATFORM=linux-arm64
      BAZEL_SHA256=cae101d31581a348774526b9d11811b04cc212c943762e6363a85a15bccfca54 ;;
    *) echo "Unsupported architecture: ${ARCH}" >&2; exit 1 ;;
  esac
  BAZEL_DIR=/usr/local/bin
elif [[ "${OS}" == "Darwin" ]]; then
  export HOMEBREW_NO_AUTO_UPDATE=1
  brew install gmp bison flex pkg-config
  case "${ARCH}" in
    x86_64)
      BAZEL_PLATFORM=darwin-x86_64
      BAZEL_SHA256=e0b57be60062f36eceed78d672088c6a2e30bd7de8674e2ee4edcd021b131c8c ;;
    arm64)
      BAZEL_PLATFORM=darwin-arm64
      BAZEL_SHA256=b1cf1c5783fa3eac60942bf2ec6169cfccecd2fa5a355587d8d35983bc1e1310 ;;
    *) echo "Unsupported architecture: ${ARCH}" >&2; exit 1 ;;
  esac
  BAZEL_DIR="$(brew --prefix)/bin"
else
  echo "Unsupported OS: ${OS}" >&2
  exit 1
fi

sha256_check() {  # <sha256> <file>
  if command -v sha256sum >/dev/null; then
    echo "$1  $2" | sha256sum -c -
  else
    echo "$1  $2" | shasum -a 256 -c -
  fi
}

fetch() {  # <url> <sha256> <output>
  curl -fsSL --retry 5 -o "$3" "$1"
  sha256_check "$2" "$3"
}

if ! command -v bazel >/dev/null; then
  fetch "https://github.com/bazelbuild/bazel/releases/download/${BAZEL_VERSION}/bazel-${BAZEL_VERSION}-${BAZEL_PLATFORM}" \
        "${BAZEL_SHA256}" "${BAZEL_DIR}/bazel"
  chmod +x "${BAZEL_DIR}/bazel"
fi

# --- Native libraries ------------------------------------------------------
if [[ -f "${PREFIX}/share/pkgconfig/ibex.pc" ]]; then
  echo "Prerequisites already installed in ${PREFIX}."
  exit 0
fi

mkdir -p "${PREFIX}"
WORK="$(mktemp -d)"
trap 'rm -rf "${WORK}"' EXIT
cd "${WORK}"

export PKG_CONFIG_PATH="${PREFIX}/lib/pkgconfig:${PREFIX}/share/pkgconfig"
if [[ "${OS}" == "Darwin" ]]; then
  # Give dylibs absolute install names so delocate can find them.
  export LDFLAGS="-Wl,-headerpad_max_install_names ${LDFLAGS:-}"
else
  export LDFLAGS="-Wl,-rpath,${PREFIX}/lib ${LDFLAGS:-}"
fi

# CoinUtils + CLP (autotools).
fetch "https://github.com/coin-or/CoinUtils/archive/refs/tags/releases/${COINUTILS_VERSION}.tar.gz" \
      "${COINUTILS_SHA256}" coinutils.tar.gz
fetch "https://github.com/coin-or/Clp/archive/refs/tags/releases/${CLP_VERSION}.tar.gz" \
      "${CLP_SHA256}" clp.tar.gz
for pkg in coinutils clp; do
  mkdir "${pkg}" && tar xzf "${pkg}.tar.gz" -C "${pkg}" --strip-components 1
  (
    cd "${pkg}"
    ./configure --prefix="${PREFIX}" --libdir="${PREFIX}/lib" \
      --enable-shared --disable-static --disable-dependency-tracking \
      --without-blas --without-lapack --without-glpk --without-asl \
      --without-mumps --without-amd --without-cholmod \
      --without-sample --without-netlib
    make -j"${JOBS}"
    make install
  )
done

# NLopt (CMake).
fetch "https://github.com/stevengj/nlopt/archive/refs/tags/v${NLOPT_VERSION}.tar.gz" \
      "${NLOPT_SHA256}" nlopt.tar.gz
mkdir nlopt && tar xzf nlopt.tar.gz -C nlopt --strip-components 1
cmake -S nlopt -B nlopt/build \
  -DCMAKE_BUILD_TYPE=Release \
  -DCMAKE_INSTALL_PREFIX="${PREFIX}" \
  -DCMAKE_INSTALL_LIBDIR=lib \
  -DCMAKE_INSTALL_NAME_DIR="${PREFIX}/lib" \
  -DBUILD_SHARED_LIBS=ON \
  -DNLOPT_PYTHON=OFF -DNLOPT_OCTAVE=OFF -DNLOPT_MATLAB=OFF \
  -DNLOPT_GUILE=OFF -DNLOPT_SWIG=OFF -DNLOPT_TESTS=OFF
cmake --build nlopt/build -j"${JOBS}"
cmake --install nlopt/build

# IBEX (waf). Uses the CLP built above.
IBEX_EXTRA_ARGS=()
if [[ "${ARCH}" != "x86_64" ]]; then
  # filib's SSE code paths (and `-msse3` in ibex.pc) are x86-only.
  IBEX_EXTRA_ARGS+=(--disable-sse2)
fi
fetch "https://github.com/dreal-deps/ibex-lib/archive/ibex-${IBEX_VERSION}.tar.gz" \
      "${IBEX_SHA256}" ibex.tar.gz
mkdir ibex && tar xzf ibex.tar.gz -C ibex --strip-components 1
(
  cd ibex
  # IBEX bundles waf 2.0.12, which predates Python 3.11/3.12 (it uses the
  # removed 'rU' file mode and the `imp` module). Unpack it and patch it.
  "${WAF_PYTHON}" ./waf --version >/dev/null 2>&1 || true  # unpacks waflib
  # waf's "prefork" runner pickles os.environ and falls back to a plain
  # subprocess only on TypeError/AttributeError. Python 3.14 raises
  # PicklingError instead, so every command "fails". Disable prefork.
  export WAF_NO_PREFORK=1
  sed -i.bak \
    -e "s/'rU'/'r'/g" \
    -e "s/^import os,re,imp,sys$/import os,re,sys/" \
    -e "s/imp\.new_module(/__import__('types').ModuleType(/g" \
    .waf3-*/waflib/Context.py .waf3-*/waflib/ConfigSet.py
  # wscript only uses distutils' LooseVersion to sort plugin names.
  sed -i.bak \
    -e 's/^from distutils.version import LooseVersion$/import re; LooseVersion = lambda s: [(0, int(t), "") if t.isdigit() else (1, 0, t) for t in re.findall(r"\\d+|\\D+", s)]/' \
    wscript
  # IBEX hard-codes -std=c++11 together with -U__STRICT_ANSI__, which breaks
  # GCC >= 13 <limits> (__float128). GNU mode never defines __STRICT_ANSI__.
  sed -i.bak -e 's/-std=c++11/-std=gnu++14/g' \
    wscript plugins/optim/wscript plugins/solver/wscript
  # On macOS, IBEX hard-codes /usr/local/bin/pkg-config (Intel Homebrew) and
  # runs it with an environment that has no PATH, so it must stay absolute.
  sed -i.bak -e "s|\[\"/usr/local/bin/pkg-config\"\]|[\"$(command -v pkg-config)\"]|" \
    plugins/lp_lib_clp/wscript
  # `-I${PREFIX}/include`: IBEX includes "coin/ClpSimplex.hpp" but only gets
  # `-I${PREFIX}/include/coin` from clp.pc (it relies on /usr/include).
  # `-include cstdint`: GCC >= 13 no longer pulls it in transitively.
  # On failure, show the logs: waf only prints "see config.log", and the
  # third-party configure scripts it runs (e.g. filib) log there too.
  dump_logs() {
    set +x
    find . -name config.log -print | while read -r log; do
      echo "===== ${log} (last 200 lines) ====="
      tail -n 200 "${log}"
    done
    return 1
  }
  CXXFLAGS="-I${PREFIX}/include -include cstdint ${CXXFLAGS:-}" "${WAF_PYTHON}" ./waf configure \
    --prefix="${PREFIX}" \
    --enable-shared \
    --with-optim \
    --with-solver \
    --with-affine-extended \
    --interval-lib=filib \
    --lp-lib=clp \
    --clp-path="${PREFIX}" \
    ${IBEX_EXTRA_ARGS[@]+"${IBEX_EXTRA_ARGS[@]}"} || dump_logs
  # IBEX's build is not parallel-safe (ibex-team/ibex-lib#286).
  "${WAF_PYTHON}" ./waf install -j1 || dump_logs
)

if [[ "${OS}" == "Darwin" ]]; then
  # Make every dylib's install name absolute (waf leaves bare names).
  for lib in "${PREFIX}"/lib/*.dylib; do
    [[ -L "${lib}" ]] || install_name_tool -id "${lib}" "${lib}"
  done
fi

echo "dReal prerequisites installed in ${PREFIX}."
