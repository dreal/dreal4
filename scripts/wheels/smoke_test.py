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
"""Runs dReal's Python unit tests against an *installed* dreal wheel.

Used by cibuildwheel's `test-command`. Run it from outside the source tree so
that `import dreal` resolves to the installed package.
"""
import os
import sys
import unittest

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), '..', '..'))
TEST_DIR = os.path.join(ROOT, 'dreal', 'test', 'python')
# Needs a test-only extension module that is not shipped in the wheel.
SKIP = {'odr_test'}


def main():
    import dreal
    location = os.path.abspath(dreal.__file__)
    print('dreal {} from {}'.format(dreal.__version__, location))
    if location.startswith(os.path.join(ROOT, 'dreal') + os.sep):
        sys.exit('dreal was imported from the source tree, not the wheel.')

    suite = unittest.TestSuite()
    for name in sorted(os.listdir(TEST_DIR)):
        module, ext = os.path.splitext(name)
        if ext != '.py' or module in SKIP:
            continue
        suite.addTests(unittest.defaultTestLoader.discover(
            TEST_DIR, pattern=name, top_level_dir=TEST_DIR))
    result = unittest.TextTestRunner(verbosity=1).run(suite)
    sys.exit(0 if result.wasSuccessful() else 1)


if __name__ == '__main__':
    main()
