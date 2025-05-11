#!/bin/bash

mv config.h config.h.bak
rm -f *.txt *.cc *.h
git clone --depth 1 https://github.com/gtkwave/libfst fst_upstream
rm fst_upstream/src/meson.build
mv fst_upstream/src/*.{h,c} .
mv fst_upstream/doc/block_format.txt .
rm -rf fst_upstream

for src in *.c; do
    mv -- "$src" "${src%.c}.cc"
done
mv config.h.bak config.h

sed -i -e 's,<config.h>,"config.h",' *.cc *.h
sed -i -e 's,"fastlz.c","fastlz.cc",' *.cc *.h

patch -p0 < 00_PATCH_win_zlib.patch
patch -p0 < 00_PATCH_win_io.patch
patch -p1 < 00_PATCH_strict_alignment.patch
patch -p0 < 00_PATCH_wx_len_overread.patch
patch -p0 < 00_PATCH_i386_endian.patch
