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
from __future__ import absolute_import
from __future__ import division
from __future__ import print_function

import sys
import subprocess
import difflib

# 1st Argument: dreal path
#               need to check if it exists
dreal = sys.argv[1]

# 2nd Argument: smt2 formula name
smt2 = sys.argv[2]

# 3rd Argument: smt2 expected output
expected_output_filename = sys.argv[3]

options = sys.argv[4:]

with open(expected_output_filename, "r") as myfile:
    expected_output = myfile.read().strip().splitlines()

try:
    # 1. Run dReal with smt2 file
    output = subprocess.check_output([dreal, smt2] + options).decode('UTF-8')
    output = output.splitlines()
    print(output)
    # 2. Compare the output with expected output
    diff_result = list(
        difflib.unified_diff(output,
                             expected_output,
                             fromfile='output',
                             tofile='expected output',
                             lineterm=''))
    if diff_result:
        # 3. They are not the same, show the diff.
        for line in diff_result:
            print(line)
        sys.exit(1)
    else:
        # 4. They are the same.
        sys.exit(0)

except subprocess.CalledProcessError as grepexc:
    print("error code", grepexc.returncode, grepexc.output)
    sys.exit(grepexc.returncode)
