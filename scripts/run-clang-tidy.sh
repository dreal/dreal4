#!/usr/bin/env bash

LAST_ARG=${@:$#}

clang-tidy $@ -header-filter=$(realpath .) -system-headers=0 -p ./ \
           -- \
           -std=c++14 \
           -I./ \
           -x c++ \
           -I bazel-genfiles \
	   `pkg-config ibex --cflags` \
           -isystem bazel-dreal4/external/spdlog/include \
           -isystem bazel-dreal4/external/fmt \
           -isystem bazel-dreal4/external/drake_symbolic \
           -isystem bazel-dreal4/external/ezoptionparser \
           -isystem bazel-dreal4/external/gtest/googletest/include \
           -isystem bazel-dreal4/external/picosat \
           -isystem /usr/local/opt/llvm/include/c++/v1 \
           -isystem /usr/local/include \
           -isystem /usr/local/opt/flex/include \

if [ ${LAST_ARG} == "--fix" ];
then
    git-clang-format -f
fi
