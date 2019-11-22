#!/usr/bin/env python3

with open("techlibs/gowin/bram_init_16.vh", "w") as f:
    for i in range(0, 0x40):
        low = i << 8
        hi = ((i+1) << 8)-1
        snippet = "INIT[%d:%d]" % (hi, low)
        print(".INIT_RAM_%02X({%s})," % (i, snippet), file=f)
