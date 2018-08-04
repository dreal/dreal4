FROM       ubuntu:16.04
MAINTAINER soonho.kong@gmail.com

RUN mkdir /dreal4
COPY . /dreal4

# Extract version and save it at /DREAL_VERSION.
RUN cd /dreal4 \
    && echo `grep "DREAL_VERSION = " tools/dreal.bzl | cut -d '"' -f 2` > /DREAL_VERSION

# Install prerequsites.
RUN apt-get update \
      && yes "Y" | /dreal4/setup/ubuntu/16.04/install_prereqs.sh \
      && apt-get install -y --no-install-recommends libpython3.5-dev \
      && rm -rf /var/lib/apt/lists/* \
      && apt-get clean all \
# Build dReal4 and install under /usr. Note that this installs
# bindings for python2.7 under /usr/lib/python2.7/dist-packages/.
      && cd /dreal4 \
      && sed -i "s/lib\/python2.7\/site-packages/lib\/python2.7\/dist-packages/" `find dreal -name "BUILD.bazel"` \
      && bazel build //:archive \
      && tar xfz bazel-bin/archive.tar.gz \
      && cp -r opt/dreal/`cat /DREAL_VERSION`/* /usr \
      && rm -rf opt/ \
# Install python3.5, build bindings for python3.5 and install it under
# /usr/lib/python3/dist-packages.
      && sed -i "s/python2/python-3.5/" tools/pybind11.BUILD.bazel \
      && sed -i "s/lib\/python2.7/lib\/python3/" `find dreal -name "BUILD.bazel"` \
      && bazel build //:archive \
      && tar xfz bazel-bin/archive.tar.gz \
      && cp -r opt/dreal/`cat /DREAL_VERSION`/lib/python3/dist-packages/dreal /usr/lib/python3/dist-packages/ \
      && rm -rf opt/ \
# Clean up
      && rm -rf /root/.cache/bazel \
      && apt remove -y bazel bison flex g++ openjdk-8-jdk wget \
      && apt autoremove -y
