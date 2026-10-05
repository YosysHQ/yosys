#!/usr/bin/env bash
set -e -x
set -o pipefail

# Build-time dependencies
## Linux Docker Images
if command -v apk &> /dev/null; then
    apk add flex bison
fi

## Platform-independent
### just build bison if it's missing or out of date
BISON_VER="3.8.2"
BISON_SHA256SUM="9bba0214ccf7f1079c5d59210045227bcf619519840ebfa80cd3849cff5a5bf2"
which -a bison || true
if ! printf '%s\n' '%require "3.8"' '%%' 'start: ;' | bison -o /dev/null /dev/stdin ; then
	PREFIX=$PWD/bison/pfx
	rm -rf $PREFIX
	BISON_SRC=$(mktemp -d)
	(
		set -e -x
		cd $BISON_SRC
		curl --connect-timeout 5 --retry 3 -L https://ftp.gnu.org/gnu/bison/bison-${BISON_VER}.tar.xz > bison.tar.xz
		echo "$BISON_SHA256SUM bison.tar.xz" | sha256sum -c -
		tar --strip-components=1 -xJC . -f bison.tar.xz
		./configure --prefix=$PREFIX
		make install -j$(getconf _NPROCESSORS_ONLN 2>/dev/null || sysctl -n hw.ncpu)
	)
	rm -rf $BISON_SRC
fi


### The Xcode Command Line Tools ersion of flex has an Apple-specific
### extension where int is substituted for size_t in some parts of the codebase.
### This is not compatible with Yosys.
###
### Also, the AlmaLinux repos are slow.
###
### It's best to just build flex if we don't like its output.
TMP_LEXER=$(mktemp)
FLEX_VER="2.6.4"
FLEX_SHA256SUM="e87aae032bf07c26f85ac0ed3250998c37621d95f8bd748b31f15b33c45ee995"
which -a flex || true
if ! ( printf "\n%%%%\n. { }\n%%%%\n" | flex -+ -o $TMP_LEXER && grep "yyFlexLexer::LexerOutput" $TMP_LEXER | grep -v 'size_t' ) ; then
	PREFIX=$PWD/flex/pfx
	rm -rf $PREFIX
	FLEX_SRC=$(mktemp -d)
	(
		set -e -x
		cd $FLEX_SRC
		curl --connect-timeout 5 --retry 3 -L https://github.com/westes/flex/releases/download/v${FLEX_VER}/flex-${FLEX_VER}.tar.gz > flex.tar.gz
		echo "$FLEX_SHA256SUM flex.tar.gz" | sha256sum -c -
		tar --strip-components=1 -xzC . -f flex.tar.gz
		./configure --prefix=$PREFIX --disable-shared --disable-silent-rules CFLAGS=-D_GNU_SOURCE
		make install -j$(getconf _NPROCESSORS_ONLN 2>/dev/null || sysctl -n hw.ncpu)
	)
	rm -rf $FLEX_SRC
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
		curl --connect-timeout 5 --retry 3 -L "https://github.com/libffi/libffi/releases/download/v${LIBFFI_VER}/libffi-${LIBFFI_VER}.tar.gz" > libffi.tar.gz
		echo "$LIBFFI_SHA256SUM libffi.tar.gz" | sha256sum -c -
		tar --strip-components=1 -xzC . -f libffi.tar.gz
		## Ultimate libyosys.so will be shared, so we need fPIC for the static libraries
		LDFLAGS=-fPIC CFLAGS=-fPIC CXXFLAGS=-fPIC ./configure --prefix=$PREFIX --enable-static --disable-shared
		make install -j$(getconf _NPROCESSORS_ONLN 2>/dev/null || sysctl -n hw.ncpu)
	)
	rm -rf $LIBFFI_SRC
fi
