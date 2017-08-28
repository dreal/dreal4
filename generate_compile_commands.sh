#!/usr/bin/env bash
set -euo pipefail
bazel build --experimental_action_listener=//tools/actions:generate_compile_commands_listener //...
python3 tools/actions/generate_compile_commands_json.py
