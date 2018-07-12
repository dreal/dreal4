FROM       ubuntu:16.04
MAINTAINER soonho.kong@gmail.com

RUN mkdir /dreal4
COPY . /dreal4
RUN apt-get update && yes "Y" \
      | /dreal4/setup/ubuntu/16.04/install_prereqs.sh \
      && rm -rf /var/lib/apt/lists/* \
      && apt-get clean all
RUN cd /dreal4 \
      && bazel build //:archive \
      && tar xfz bazel-bin/archive.tar.gz \
      && cp -r opt/dreal/`grep "DREAL_VERSION = " tools/dreal.bzl | cut -d '"' -f 2`/* /usr
