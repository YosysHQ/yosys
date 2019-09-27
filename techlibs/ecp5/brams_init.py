#!/usr/bin/env python3
with open("techlibs/ecp5/bram_init_1_2_4.vh", "w") as f:
    for i in range(0, 0x40):
        init_snippets = []
        for j in range(32):
            init_snippets.append("INIT[%4d*8 +: 8]" % (32 * i + j))
            init_snippets.append("3'b000" if (j % 2 == 1) else "1'b0")
        init_snippets = list(reversed(init_snippets))
        for k in range(8, 64, 8):
            init_snippets[k] = "\n          " + init_snippets[k]
        print(".INITVAL_%02X({%s})," % (i, ", ".join(init_snippets)), file=f)

with open("techlibs/ecp5/bram_init_9_18_36.vh", "w") as f:
    for i in range(0, 0x40):
        init_snippets = []
        for j in range(16):
            init_snippets.append("INIT[%3d*18 +: 18]" % (16 * i + j))
            init_snippets.append("2'b00")
        init_snippets = list(reversed(init_snippets))
        for k in range(8, 32, 8):
            init_snippets[k] = "\n          " + init_snippets[k]
        print(".INITVAL_%02X({%s})," % (i, ", ".join(init_snippets)), file=f)
