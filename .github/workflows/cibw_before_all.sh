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

## macOS/Windows -- install in GitHub Action itself, not container

# Build Static FFI (platform-dependent but not Python version dependent)
cd ffi
SHELL=bash CFLAGS=-fPIC CXXFLAGS=-fPIC ./configure --prefix=$PWD/pfx

make install -j$(getconf _NPROCESSORS_ONLN 2>/dev/null || sysctl -n hw.ncpu)
sed -i.bak 's@-L${toolexeclibdir} -lffi@${toolexeclibdir}/libffi.a@' ./pfx/lib/pkgconfig/libffi.pc
