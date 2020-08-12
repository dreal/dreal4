How to Build and Install dReal on Fedora 32
===========================================

Install Prerequisites
---------------------

```bash
yum install -y \
	NLopt-devel \
	bison \
	coin-or-Clp-devel \
	findutils \
	flex \
	g++ \
	git \
	gmp-devel \
	make \
	python2 \
	which
```

Install Bazel
-------------

Follow the instructions at https://docs.bazel.build/versions/master/install-redhat.html.

```bash
dnf install dnf-plugins-core
dnf copr enable vbatts/bazel
dnf install bazel3
```

Build and Install IBEX Lib
--------------------------

```bash
curl https://codeload.github.com/dreal-deps/ibex-lib/tar.gz/fde1b111a5439eb59b7260bb84189e1a0c9cffca | tar xz
cd ibex-lib-fde1b111a5439eb59b7260bb84189e1a0c9cffca/
CXXFLAGS=-std=c++0x ./waf configure \
	--enable-shared \
	--with-optim \
	--with-solver \
	--with-affine-extended \
	--interval-lib=filib \
	--lp-lib=clp \
	--prefix=/opt/libibex/2.7.4
sudo ./waf install
```

Build and Test dReal
--------------------

```bash
git clone https://github.com/dreal/dreal4
cd dreal4
bazel build //dreal:dreal
./bazel-bin/dreal/dreal ./dreal/test/smt2/01.smt2
```
