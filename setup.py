# -*- coding: utf-8 -*-
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
"""Builds dReal's Python binding with Bazel.

Project metadata lives in pyproject.toml. This file only adds the native build
step: `build_py` runs Bazel to produce `_dreal_py.so` and `libdreal_.so` and
places them in the `dreal` package.

The resulting wheel still links against IBEX, CLP, NLopt and GMP from the build
machine. Release wheels are built with cibuildwheel, which repairs them with
auditwheel (Linux) or delocate (macOS) so that those libraries are bundled into
the wheel and end users need nothing besides `pip install dreal`. See
`[tool.cibuildwheel]` in pyproject.toml.

Environment variables:
  BAZEL             Bazel executable (default: `bazel`, then `bazelisk`).
  DREAL_BAZEL_ARGS  Extra arguments passed to `bazel build`.
"""
import os
import shlex
import shutil
import subprocess
import sys

import setuptools
from setuptools.command.build_py import build_py as _build_py
from setuptools.dist import Distribution

VERSION = '4.21.06.2'.replace(".0", ".")
ROOT_DIR = os.path.abspath(os.path.dirname(__file__))
PKG_DIR = os.path.join(ROOT_DIR, 'dreal')

# Bazel target -> path under bazel-bin.
NATIVE_LIBS = {
    '//dreal:_dreal_py.so': os.path.join('dreal', '_dreal_py.so'),
    '//:libdreal_.so': 'libdreal_.so',
}

PREREQS_HELP = (
    "Building dReal from source requires Bazel and dReal's prerequisites "
    "(IBEX, CLP, NLopt, GMP, bison, flex). scripts/wheels/install_deps.sh "
    "builds them on manylinux and macOS; on Ubuntu you can also use "
    "setup/ubuntu/<version>/install_prereqs.sh. Prebuilt wheels on PyPI bundle "
    "these libraries and need none of them.")


def _find_bazel():
    candidates = [os.environ['BAZEL']] if 'BAZEL' in os.environ else [
        'bazel', 'bazelisk']
    for candidate in candidates:
        path = shutil.which(candidate)
        if path:
            return path
    raise RuntimeError('Bazel not found.\n' + PREREQS_HELP)


def _build_native():
    bazel = _find_bazel()
    env = dict(os.environ, PYTHON_BIN_PATH=sys.executable)
    common = ['--repo_env=PYTHON_BIN_PATH=' + sys.executable]
    if sys.platform == 'darwin' and os.environ.get('MACOSX_DEPLOYMENT_TARGET'):
        # Bazel ignores MACOSX_DEPLOYMENT_TARGET and defaults to the SDK's
        # version, which delocate then rejects.
        common.append('--macos_minimum_os=' +
                      os.environ['MACOSX_DEPLOYMENT_TARGET'])
    extra = shlex.split(os.environ.get('DREAL_BAZEL_ARGS', ''))
    try:
        subprocess.run([bazel, 'build', *common, *NATIVE_LIBS,
                        '--cxxopt=-DDREAL_CHECK_INTERRUPT', *extra],
                       cwd=ROOT_DIR, env=env, check=True)
        bazel_bin = subprocess.run(
            [bazel, 'info', *common, *extra, 'bazel-bin'],
            cwd=ROOT_DIR, env=env, check=True, stdout=subprocess.PIPE,
            universal_newlines=True).stdout.strip()
    except subprocess.CalledProcessError:
        raise RuntimeError('Unable to build dReal.\n' + PREREQS_HELP)

    for src in NATIVE_LIBS.values():
        dst = os.path.join(PKG_DIR, os.path.basename(src))
        if os.path.lexists(dst):
            os.remove(dst)  # Bazel outputs are read-only.
        shutil.copyfile(os.path.join(bazel_bin, src), dst)
        os.chmod(dst, 0o755)

    if sys.platform == 'darwin':
        _fix_macos_install_names()


def _fix_macos_install_names():
    """Makes _dreal_py.so load libdreal_.so from its own directory."""
    dst = os.path.join(PKG_DIR, '_dreal_py.so')
    subprocess.check_call(
        ['install_name_tool', '-id', '@rpath/_dreal_py.so', dst])
    output = subprocess.check_output(['otool', '-L', dst],
                                     universal_newlines=True)
    for line in output.splitlines()[1:]:
        path = line.split(' (')[0].strip()
        if path.endswith('libdreal_.so') and \
                path != '@loader_path/libdreal_.so':
            subprocess.check_call([
                'install_name_tool', '-change', path,
                '@loader_path/libdreal_.so', dst
            ])


class build_py(_build_py):
    def run(self):
        self.execute(_build_native, (), msg='Building dReal with Bazel')
        _build_py.run(self)


class BinaryDistribution(Distribution):
    """Marks the wheel as platform- and CPython-version-specific.

    The native libraries are built by Bazel rather than as setuptools
    extensions, so tell setuptools that the package has extension modules.
    """
    def has_ext_modules(self):
        return True


setuptools.setup(
    version=VERSION,
    distclass=BinaryDistribution,
    cmdclass={'build_py': build_py},
)
