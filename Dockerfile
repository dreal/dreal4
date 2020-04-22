FROM       ubuntu:18.04

RUN mkdir /dreal4
COPY . /dreal4
WORKDIR /dreal4
# Extract version and save it at /DREAL_VERSION.
RUN echo `grep "DREAL_VERSION = " tools/dreal.bzl | cut -d '"' -f 2` > /DREAL_VERSION

# Install prerequisites.
ARG DEBIAN_FRONTEND=noninteractive
RUN apt-get update \
      && yes "Y" | /dreal4/setup/ubuntu/18.04/install_prereqs.sh \
      && apt-get install -y --no-install-recommends apt-utils python3-dev python3-wheel python3-setuptools python3-pip python \
      && rm -rf /var/lib/apt/lists/* \
      && apt-get clean all \
# Build dReal4
      && cd /dreal4 \
      && bazel build //:archive \
      && tar xfz bazel-bin/archive.tar.gz --strip-components 4 -C /usr \
# Install Python3 Binding
      && python3 setup.py bdist_wheel \
      && pip3 install ./dist/dreal-`cat /DREAL_VERSION`-cp36-none-manylinux1_x86_64.whl \
      && bazel clean --expunge \
# Clean up
      && cd / \
      && rm -rf dreal4 \
      && rm -rf /root/.cache/bazel \
      && rm -rf /var/lib/apt/lists/* \
      && apt-get remove -y bazel bison flex g++ wget python \
      && apt-get autoclean -y \
      && apt-get autoremove -y
