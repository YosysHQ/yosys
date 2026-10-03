#!/usr/bin/env bash
set -e -x

# Build-time dependencies
## Linux Docker Images
if command -v yum &> /dev/null; then
    yum install -y flex # manylinux's bison versions are hopelessly out of date
fi

if command -v apk &> /dev/null; then
    apk add flex bison
fi

## Platform-independent - just build bison if it's missing or out of date
BISON_VER="3.8.2"
BISON_SHA256SUM="9bba0214ccf7f1079c5d59210045227bcf619519840ebfa80cd3849cff5a5bf2"
if ! printf '%s\n' '%require "3.8"' '%%' 'start: ;' | bison -o /dev/null /dev/stdin ; then
	PREFIX=$PWD/bison/pfx
	rm -rf $PREFIX
	BISON_SRC=$(mktemp -d)
	(
		set -e -x
		cd $BISON_SRC
		curl -L https://ftp.gnu.org/gnu/bison/bison-3.8.2.tar.xz > bison.tar.xz
		echo "$BISON_SHA256SUM bison.tar.xz" | sha256sum -c -
		tar --strip-components=1 -xJC . -f bison.tar.xz
		./configure --prefix=$PREFIX
		make clean
		make install -j$(getconf _NPROCESSORS_ONLN 2>/dev/null || sysctl -n hw.ncpu)
	)
	rm -rf $BISON_SRC
fi

# Runtime Dependencies
## Build Static FFI (platform-dependent but not Python version dependent) if
## missing
LIBFFI_VER="3.4.8"
LIBFFI_SHA256SUM="bc9842a18898bfacb0ed1252c4febcc7e78fa139fd27fdc7a3e30d9d9356119b"
if ! echo "int main() {}" | cc -x c -l:libffi.a - ; then
	PREFIX=$PWD/ffi/pfx
	rm -rf $PREFIX
	LIBFFI_SRC=$(mktemp -d)
	(
		set -e -x
		cd $LIBFFI_SRC
		curl -L "https://github.com/libffi/libffi/releases/download/v${LIBFFI_VER}/libffi-${LIBFFI_VER}.tar.gz" > libffi.tar.gz
		echo "$LIBFFI_SHA256SUM libffi.tar.gz" | sha256sum -c -
		tar --strip-components=1 -xzC . -f libffi.tar.gz
		## Ultimate libyosys.so will be shared, so we need fPIC for the static libraries
		LDFLAGS=-fPIC CFLAGS=-fPIC CXXFLAGS=-fPIC ./configure --prefix=$PREFIX --enable-static --disable-shared
		make install -j$(getconf _NPROCESSORS_ONLN 2>/dev/null || sysctl -n hw.ncpu)
		PKG_CONFIG_PATH=$PREFIX/lib/pkgconfig pkg-config libffi --validate
	)
	rm -rf $LIBFFI_SRC
fi
