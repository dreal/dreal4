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

# io.open is needed for projects that support Python 2.7
# It ensures open() defaults to text mode with universal newlines,
# and accepts an argument to specify the text encoding
# Python 3 only projects can skip this import
from io import open

VERSION = '4.19.04.2'.replace(".0", ".")
ROOT_DIR = os.path.abspath(os.path.dirname(__file__))
SRC_DIR = os.path.join(ROOT_DIR)


def _build_dreal():
    if sys.version_info.major == 2:
        PYTHON_VERSION = 'PY2'
    else:
        PYTHON_VERSION = 'PY3'
    if subprocess.call([
            'bazel',
            'build',
            '//:libdreal.so',
            '//dreal:_dreal_py.so',
            '--python_path={}'.format(sys.executable),
            '--python_version={}'.format(PYTHON_VERSION),
    ]) != 0:
        raise LibError("Unable to build dReal.\n" +
                       "Please visit https://pypi.org/project/dreal and " +
                       "follow the instructions to install the prerequsites.")


def _copy_bins():
    shutil.copy(
        os.path.join(SRC_DIR, 'bazel-bin', 'dreal', '_dreal_py.so'),
        os.path.join(ROOT_DIR, 'dreal'))
    os.chmod(os.path.join(ROOT_DIR, 'dreal', '_dreal_py.so'), 436)
    shutil.copy(
        os.path.join(SRC_DIR, 'bazel-bin', 'libdreal.so'),
        os.path.join(ROOT_DIR, 'dreal'))
    os.chmod(os.path.join(ROOT_DIR, 'dreal', 'libdreal.so'), 436)
    if sys.platform == 'darwin':
        if subprocess.call([
                '/usr/bin/install_name_tool',
                '-change',
                '@rpath/libdreal.so',
                '@loader_path/libdreal.so',
                os.path.join(ROOT_DIR, 'dreal', '_dreal_py.so'),
        ]) != 0:
            raise LibError("Unable to use install_name_tool.")


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


# Get the long description from the README file
here = os.path.abspath(os.path.dirname(__file__))
with open(os.path.join(here, 'README_PIP.md'), encoding='utf-8') as f:
    long_description = f.read()

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
    # For example, "cp35" or "cp27".
    if not any(arg.startswith('--python-tag') for arg in sys.argv):
        import wheel.pep425tags
        python_tag = "%s%d%d" % (wheel.pep425tags.get_abbr_impl(),
                                 sys.version_info.major,
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
        'Programming Language :: Python :: 2',
        'Programming Language :: Python :: 2.7',
        'Programming Language :: Python :: 3',
        'Programming Language :: Python :: 3.5',
        'Programming Language :: Python :: 3.6',
        'Programming Language :: Python :: 3.7',
        'Operating System :: POSIX :: Linux',
        'Operating System :: MacOS',
    ],
    keywords=['dreal', 'smt', 'theorem', 'prover'],  # Optional
    packages=['dreal'],
    include_package_data=True,
    package_data={  # Optional
        'dreal': ['_dreal_py.so', 'libdreal.so'],
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
