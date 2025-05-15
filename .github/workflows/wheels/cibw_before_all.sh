set -e
set -x

# Build-time dependencies
## Linux Docker Images
if command -v yum &> /dev/null; then
    yum install -y flex bison
fi

if command -v apk &> /dev/null; then
    apk add flex bison
fi

## macOS/Windows -- installed in GitHub Action itself, not container

# Build Static FFI (platform-dependent but not Python version dependent)
cd ffi
## Ultimate libyosys.so will be shared, so we need fPIC for the static libraries
CFLAGS=-fPIC CXXFLAGS=-fPIC ./configure --prefix=$PWD/pfx
## Without this, SHELL has a space in its path which breaks the makefile
make install -j$(getconf _NPROCESSORS_ONLN 2>/dev/null || sysctl -n hw.ncpu)
## Forces static library to be used in all situations
sed -i.bak 's@-L${toolexeclibdir} -lffi@${toolexeclibdir}/libffi.a@' ./pfx/lib/pkgconfig/libffi.pc
