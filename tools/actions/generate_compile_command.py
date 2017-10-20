# This is the implementation of a Bazel extra_action which genenerates
# _compile_command files for generate_compile_commands.py to consume.

import sys

import tools.third_party.com_github_bazelbuild_bazel.protos.extra_actions_base_pb2 as extra_actions_base_pb2

def _get_cpp_command(cpp_compile_info):
  compiler = cpp_compile_info.tool
  options = ' '.join(cpp_compile_info.compiler_option)
  source = cpp_compile_info.source_file
  output = cpp_compile_info.output_file
  return '%s %s -c %s -o %s' % (compiler, options, source, output), source

def main(argv):
  action = extra_actions_base_pb2.ExtraActionInfo()
  with open(argv[1], 'rb') as f:
    action.MergeFromString(f.read())
  command, source_file = _get_cpp_command(
      action.Extensions[extra_actions_base_pb2.CppCompileInfo.cpp_compile_info])
  with open(argv[2], 'w') as f:
    f.write(command)
    f.write('\0')
    f.write(source_file)

if __name__ == '__main__':
  sys.exit(main(sys.argv))
