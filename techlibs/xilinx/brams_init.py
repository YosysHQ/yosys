#!/usr/bin/env python3

with open("techlibs/xilinx/brams_init_9.vh", "w") as f:
    for i in range(4):
        init_snippets = [" INIT[%3d*9+8]" % (k+256*i,) for k in range(255, -1, -1)]
        for k in range(4, 256, 4):
            init_snippets[k] = "\n           " + init_snippets[k]
        print(".INITP_%02X({%s})," % (i, ",".join(init_snippets)), file=f)
    for i in range(32):
        init_snippets = [" INIT[%3d*9 +: 8]" % (k+32*i,) for k in range(31, -1, -1)]
        for k in range(4, 32, 4):
            init_snippets[k] = "\n          " + init_snippets[k]
        print(".INIT_%02X({%s})," % (i, ",".join(init_snippets)), file=f)

with open("techlibs/xilinx/brams_init_18.vh", "w") as f:
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

with open("techlibs/xilinx/brams_init_36.vh", "w") as f:
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

with open("techlibs/xilinx/brams_init_8.vh", "w") as f:
    for i in range(32):
        print(".INIT_%02X(INIT[%3d*256 +: 256])," % (i, i), file=f)

with open("techlibs/xilinx/brams_init_16.vh", "w") as f:
    for i in range(64):
        print(".INIT_%02X(INIT[%3d*256 +: 256])," % (i, i), file=f)

with open("techlibs/xilinx/brams_init_32.vh", "w") as f:
    for i in range(128):
        print(".INIT_%02X(INIT[%3d*256 +: 256])," % (i, i), file=f)

