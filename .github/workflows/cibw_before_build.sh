set -e
set -x

# Build boost
cd ./boost
## Delete the artefacts from previous builds (if any)
rm -rf ./pfx
## Bootstrap bjam
./bootstrap.sh --prefix=./pfx
## Build Boost against current version of Python, only for
## static linkage (Boost is statically linked because system boost packages
## wildly vary in versions, including the libboost_python3 version)
./b2\
    -j$(getconf _NPROCESSORS_ONLN 2>/dev/null || sysctl -n hw.ncpu)\
    --prefix=./pfx\
    --with-filesystem\
    --with-system\
    --with-python\
    cxxflags="$(python3-config --includes) -std=c++17 -fPIC"\
    cflags="$(python3-config --includes) -fPIC"\
    link=static\
    variant=release\
    install
