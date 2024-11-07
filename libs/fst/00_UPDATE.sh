#!/bin/bash

mv config.h config.h.bak
rm -f *.txt *.cc *.h
git clone --depth 1 https://github.com/gtkwave/gtkwave fst_upstream
rm fst_upstream/lib/libfst/CMakeLists.txt
mv fst_upstream/lib/libfst/*.{h,c,txt} .
rm -rf fst_upstream

for src in *.c; do
    mv -- "$src" "${src%.c}.cc"
done
mv config.h.bak config.h

sed -i -e 's,<config.h>,"config.h",' *.cc *.h
sed -i -e 's,"fastlz.c","fastlz.cc",' *.cc *.h

patch -p0 < 00_PATCH_win_zlib.patch
patch -p0 < 00_PATCH_win_io.patch
