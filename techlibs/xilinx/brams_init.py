#!/usr/bin/env python3

from __future__ import absolute_import
from __future__ import division
from __future__ import print_function

import argparse
import os

parser = argparse.ArgumentParser(description='Generate Xilinx bram initializations')
parser.add_argument('--output_directory', default=os.path.dirname(__file__))
args = parser.parse_args()

init_18_path = os.path.join(args.output_directory, "brams_init_18.vh")
with open(init_18_path, "w") as f:
    for i in range(8):
        init_snippets = [" INIT[%3d*9+8]" % (k+256*i,) for k in range(255, -1, -1)]
        for k in range(4, 256, 4):
            init_snippets[k] = "\n           " + init_snippets[k]
        print(".INITP_%02X({%s})," % (i, ",".join(init_snippets)), file=f)
    for i in range(64):
        init_snippets = [" INIT[%3d*9 +: 8]" % (k+32*i,) for k in range(31, -1, -1)]
        for k in range(4, 32, 4):
            init_snippets[k] = "\n          " + init_snippets[k]
        print(".INIT_%02X({%s})," % (i, ",".join(init_snippets)), file=f)

init_36_path = os.path.join(args.output_directory, "brams_init_36.vh")
with open(init_36_path, "w") as f:
    for i in range(16):
        init_snippets = [" INIT[%3d*9+8]" % (k+256*i,) for k in range(255, -1, -1)]
        for k in range(4, 256, 4):
            init_snippets[k] = "\n           " + init_snippets[k]
        print(".INITP_%02X({%s})," % (i, ",".join(init_snippets)), file=f)
    for i in range(128):
        init_snippets = [" INIT[%3d*9 +: 8]" % (k+32*i,) for k in range(31, -1, -1)]
        for k in range(4, 32, 4):
            init_snippets[k] = "\n          " + init_snippets[k]
        print(".INIT_%02X({%s})," % (i, ",".join(init_snippets)), file=f)

init_16_path = os.path.join(args.output_directory, "brams_init_16.vh")
with open(init_16_path, "w") as f:
    for i in range(64):
        print(".INIT_%02X(INIT[%3d*256 +: 256])," % (i, i), file=f)

init_32_path = os.path.join(args.output_directory, "brams_init_32.vh")
with open(init_32_path, "w") as f:
    for i in range(128):
        print(".INIT_%02X(INIT[%3d*256 +: 256])," % (i, i), file=f)

