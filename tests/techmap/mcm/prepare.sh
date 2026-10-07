#!/bin/sh

set -e

DIR=$(dirname "$0")

wget https://spiral.ece.cmu.edu/mcm/dl/synth-jan-14-2009.tar.gz -O "$DIR/synth-jan-14-2009.tar.gz"
tar -xzf "$DIR/synth-jan-14-2009.tar.gz" --directory "$DIR/"
rm "$DIR/synth-jan-14-2009.tar.gz"
mv "$DIR/synth-jan-14-2009" "$DIR/synth"
patch -d "$DIR/synth" -p1 < "$DIR/synth.patch"
