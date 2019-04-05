FROM       ubuntu:18.04
MAINTAINER soonho.kong@gmail.com

RUN mkdir /dreal4
COPY . /dreal4

# Extract version and save it at /DREAL_VERSION.
RUN cd /dreal4 \
    && echo `grep "DREAL_VERSION = " tools/dreal.bzl | cut -d '"' -f 2` > /DREAL_VERSION

# Install prerequsites.
RUN apt-get update \
      && yes "Y" | /dreal4/setup/ubuntu/18.04/install_prereqs.sh \
      && apt-get install -y --no-install-recommends python3-dev \
      && rm -rf /var/lib/apt/lists/* \
      && apt-get clean all \
# Build dReal4 and install under /usr. Note that this installs
# bindings for python2.7 under /usr/lib/python2.7/dist-packages/.
      && cd /dreal4 \
      && sed -i "s/site-packages/dist-packages/" tools/dreal.bzl \
      && bazel build //:archive \
      && tar xfz bazel-bin/archive.tar.gz \
      && cp -r opt/dreal/`cat /DREAL_VERSION`/* /usr \
      && rm -rf opt/ \
# Install python3.6, build bindings for python3 and install it under
# /usr/lib/python3/dist-packages.
      && bazel build //:archive --python_version=py3 --python_path=python3 \
      && tar xfz bazel-bin/archive.tar.gz \
      && cp -r opt/dreal/`cat /DREAL_VERSION`/lib/python3/dist-packages/dreal /usr/lib/python3/dist-packages/ \
      && rm -rf opt/ \
# Clean up
      && rm -rf /root/.cache/bazel \
      && apt remove -y bazel bison flex g++ wget \
      && apt autoremove -y
