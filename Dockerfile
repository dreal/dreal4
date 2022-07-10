FROM       ubuntu:20.04

RUN mkdir /dreal4
COPY . /dreal4
WORKDIR /dreal4

# Install prerequisites.
ARG DEBIAN_FRONTEND=noninteractive
RUN apt-get update \
      && yes "Y" | /dreal4/setup/ubuntu/20.04/install_prereqs.sh \
      && apt-get install -y --no-install-recommends apt-utils python3-dev python3-wheel python3-setuptools python3-pip python-is-python3 \
      && rm -rf /var/lib/apt/lists/* \
      && apt-get clean all \
# Build dReal4
      && cd /dreal4 \
      && bazel build //:archive \
      && tar xfz bazel-bin/archive.tar.gz --strip-components 3 -C /usr \
# Install Python3 Binding
      && python3 setup.py bdist_wheel \
      && pip3 install ./dist/dreal-*-cp38-none-manylinux1_x86_64.whl \
      && bazel clean --expunge \
# Clean up
      && cd / \
      && rm -rf dreal4 \
      && rm -rf /root/.cache/bazel \
      && rm -rf /var/lib/apt/lists/* \
      && apt-get remove -y bazel bison flex g++ wget \
      && apt-get autoclean -y \
      && apt-get autoremove -y
