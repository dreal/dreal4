# -*- python -*-
# This file contains rules for Bazel

def dreal_dr_tests(data):
    prefix = "dreal/test/dr"
    for dr in native.glob(["*.dr"]):
        native.py_test(
            name = "run_" + dr,
            args = [
                "$(location //dreal:dreal)",
                prefix + "/" + dr,
                prefix + "/" + dr + ".expected",
            ],
            tags = ["dr"],
            srcs = ["test.py"],
            data = ["//dreal:dreal",
                    ":dr"],
            main = "test.py",
        )
