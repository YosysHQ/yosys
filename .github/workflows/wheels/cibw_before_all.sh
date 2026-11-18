#!/usr/bin/env bash
set -e -x
set -o pipefail

# Build-time dependencies
## Linux Docker Images
if command -v apk &> /dev/null; then
	apk add flex bison
fi

## Platform-independent
### Installing ccache on RHEL is a pain and pulls in libfmt on macOS which
### slang jumps on immediately and refuses to compile its own libfmt, causing
### wheel delocation to fail (Homebrew libraries are built per-OS).
###
### might as well just install them all the same way, each tarball is like 2MiB
CCACHE_VER=4.14.3
if ! command -v ccache &> /dev/null; then
	CCACHE_BIN=$(mktemp -d)
	id=$(uname)-$(uname -m)
	case $id in
		Linux-x86_64)
			id=linux-x86_64-musl-static
			CCACHE_SHA256SUM="e4583fd653b794a480b9915358679a75cdd7a7010dd865eaf4cbdc61e665a3f0"
			;;
		Linux-aarch64)
			id=linux-aarch64-musl-static
			CCACHE_SHA256SUM="4b0ecece7929cbaf548ff1ab9a24074b240132ab8176bc3865a27d88c457a0d8"
			;;
		Darwin*)
			# universal
			id=darwin
			CCACHE_SHA256SUM="764dd2a8100ff83e6bbd7b9a1e2016cc401be34bee8a70ea99698186622c34d5"
			;;
	esac
	mkdir -p $PWD/ccache/bin
	curl --connect-timeout 5 --retry 3 -L https://github.com/ccache/ccache/releases/download/v$CCACHE_VER/ccache-$CCACHE_VER-$id.tar.gz > ccache/ccache.tgz
	echo "$CCACHE_SHA256SUM ccache/ccache.tgz" | sha256sum -c -
	tar -xzC $PWD/ccache/bin --strip-components 1 -f ccache/ccache.tgz
fi

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
		./configure --prefix=$PREFIX CC="ccache ${CC:-cc}" CXX="ccache ${CXX:-c++}"
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
		./configure --prefix=$PREFIX --disable-shared --disable-silent-rules CFLAGS=-D_GNU_SOURCE CC="ccache ${CC:-cc}" CXX="ccache ${CXX:-c++}"
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
		CC="ccache ${CC:-cc}" CXX="ccache ${CXX:-c++}" LDFLAGS=-fPIC CFLAGS=-fPIC CXXFLAGS=-fPIC ./configure --prefix=$PREFIX --enable-static --disable-shared
		make install -j$(getconf _NPROCESSORS_ONLN 2>/dev/null || sysctl -n hw.ncpu)
	)
	rm -rf $LIBFFI_SRC
fi
