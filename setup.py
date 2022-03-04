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
import os
import platform
import setuptools
import shutil
import subprocess
import sys

from distutils.command.build import build as _build
from distutils.command.sdist import sdist as _sdist
from distutils.errors import LibError
from distutils.util import get_platform
from setuptools.command.bdist_egg import bdist_egg as _bdist_egg
from setuptools.command.develop import develop as _develop

VERSION = '4.21.06.2'.replace(".0", ".")
ROOT_DIR = os.path.abspath(os.path.dirname(__file__))
SRC_DIR = os.path.join(ROOT_DIR)


def _build_dreal():
    new_env = os.environ.copy()
    new_env["PYTHON_BIN_PATH"] = sys.executable
    if subprocess.call([
            'bazel', 'build', '//dreal:_dreal_py.so',
            '--cxxopt=-DDREAL_CHECK_INTERRUPT', '--python_path={}'.format(
                sys.executable),
    ],
                       env=new_env) != 0:
        raise LibError("Unable to build dReal.\n" +
                       "Please visit https://pypi.org/project/dreal and " +
                       "follow the instructions to install the prerequisites.")


def _copy_bins():
    shutil.copy(os.path.join(SRC_DIR, 'bazel-bin', 'dreal', '_dreal_py.so'),
                os.path.join(ROOT_DIR, 'dreal'))
    os.chmod(os.path.join(ROOT_DIR, 'dreal', '_dreal_py.so'), 436)
    shutil.copy(os.path.join(SRC_DIR, 'bazel-bin', 'libdreal_.so'),
                os.path.join(ROOT_DIR, 'dreal'))
    os.chmod(os.path.join(ROOT_DIR, 'dreal', 'libdreal_.so'), 436)
    if sys.platform == 'darwin':
        dst_full = os.path.join(ROOT_DIR, 'dreal', '_dreal_py.so')
        subprocess.check_call(
            ["install_name_tool",
             "-id",
             os.path.join('@rpath', "_dreal_py.so"),
             dst_full])
        file_output = subprocess.check_output(["otool",
                                               "-L",
                                               dst_full]).decode("utf-8")
        for line in file_output.splitlines():
            # keep only file path, remove version information.
            relative_path = line.split(' (')[0].strip()
            # If path is relative, it needs to be replaced by absolute path.
            if "@loader_path" not in relative_path:
                continue
            if "libdreal_.so" in relative_path:
                subprocess.check_call(
                    ["install_name_tool",
                     "-change", relative_path,
                     os.path.join('@loader_path', "libdreal_.so"),
                     dst_full])


class build(_build):
    def run(self):
        self.execute(_build_dreal, (), msg="Building dReal")
        self.execute(_copy_bins, (), msg="Copying binaries")
        _build.run(self)


class develop(_develop):
    def run(self):
        self.execute(_build_dreal, (), msg="Building dReal")
        self.execute(_copy_bins, (), msg="Copying binaries")
        _develop.run(self)


class bdist_egg(_bdist_egg):
    def run(self):
        self.run_command('build')
        _bdist_egg.run(self)


class sdist(_sdist):
    def run(self):
        self.run_command('build')
        _sdist.run(self)


long_description = """dReal4: SMT Solver for Nonlinear Theories of Reals

Please visit https://github.com/dreal/dreal4.


Precompiled Wheels
------------------

We provide precompiled distributions (`.whl`) for the following environments:

 - macOS 11.0 / 10.15 + CPython 3
 - Linux + CPython 3.7 / 3.8 / 3.9 / 3.10

You still need to install dReal prerequisites such as IBEX and CLP in
your system. To install them, please follow the instructions below:

macOS 11.0 / 10.15

    brew tap robotlocomotion/director
    brew tap dreal/dreal
    brew install dreal --only-dependencies

Ubuntu 20.04 / 18.04

    curl -fsSL https://raw.githubusercontent.com/dreal/dreal4/master/setup/ubuntu/`lsb_release -r -s`/install.sh | sudo bash


Build from Source
-----------------

If `pip` fails to find a precompiled distribution, it fetches dReal
source and build it from scratch. You need to install the required
packages to do so. To install them, please follow the instructions
below:

macOS 11.0 / 10.15

    brew tap robotlocomotion/director
    brew tap dreal/dreal
    brew install dreal --only-dependencies --build-from-source

Ubuntu 20.04 / 18.04

    curl -fsSL https://raw.githubusercontent.com/dreal/dreal4/master/setup/ubuntu/`lsb_release -r -s`/install_prereqs.sh | sudo bash

"""

if 'bdist_wheel' in sys.argv and '--plat-name' not in sys.argv:
    idx = sys.argv.index('bdist_wheel') + 1
    sys.argv.insert(idx, '--plat-name')
    name = get_platform()
    if 'linux' in name:
        # linux_* platform tags are disallowed because the python
        # ecosystem is fubar linux builds should be built in the
        # centos 5 vm for maximum compatibility see
        # https://github.com/pypa/manylinux see also
        # https://github.com/angr/angr-dev/blob/master/admin/bdist.py
        sys.argv.insert(idx + 1, 'manylinux1_' + platform.machine())
    elif 'mingw' in name:
        if platform.architecture()[0] == '64bit':
            sys.argv.insert(idx + 1, 'win_amd64')
        else:
            sys.argv.insert(idx + 1, 'win32')
    else:
        # https://www.python.org/dev/peps/pep-0425/
        sys.argv.insert(idx + 1, name.replace('.', '_').replace('-', '_'))

    # Make a wheel which is specific to the minor version of Python
    # For example, "cp35".
    #
    # Note: We assume that it's using cpython.
    if not any(arg.startswith('--python-tag') for arg in sys.argv):
        python_tag = "cp%d%d" % (sys.version_info.major,
                                 sys.version_info.minor)
        sys.argv.extend(['--python-tag', python_tag])

setuptools.setup(
    name='dreal',  # Required
    version=VERSION,  # Required
    description='SMT Solver for Nonlinear Theories of Reals',  # Optional
    long_description=long_description,  # Optional
    long_description_content_type='text/markdown',  # Optional (see note above)
    url='https://github.com/dreal/dreal4',  # Optional
    author='Soonho Kong',  # Optional
    author_email='soonho.kong@gmail.com',  # Optional
    classifiers=[  # Optional
        'License :: OSI Approved :: Apache Software License',
        'Programming Language :: Python :: 3',
        'Programming Language :: Python :: 3.7',
        'Programming Language :: Python :: 3.8',
        'Programming Language :: Python :: 3.9',
        'Programming Language :: Python :: 3.10',
        'Operating System :: POSIX :: Linux',
        'Operating System :: MacOS',
    ],
    keywords=['dreal', 'smt', 'theorem', 'prover'],  # Optional
    packages=['dreal'],
    include_package_data=True,
    package_data={  # Optional
        'dreal': ['_dreal_py.so', 'libdreal_.so'],
    },
    project_urls={  # Optional
        'Bug Reports': 'https://github.com/dreal/dreal4/issues',
        'Source': 'https://github.com/dreal/dreal4',
    },
    cmdclass={'build': build,
              'develop': develop,
              'sdist': sdist,
              'bdist_egg': bdist_egg},
)
