#!/usr/bin/env python3
with open("techlibs/quicklogic/bram_init_8_16.vh", "w") as f:
    init_snippets = []
    for i in range(0, 2048):
        init_snippets.append("INIT[%4d*8 +: 8]" % (i))
        init_snippets.append("1'b0")
    init_snippets = list(reversed(init_snippets))
    for k in range(8, 4096, 8):
        init_snippets[k] = "\n          " + init_snippets[k]
    print(".INIT({%s})," % (", ".join(init_snippets)), file=f)

with open("techlibs/quicklogic/bram_init_32.vh", "w") as f:
    init_snippets = []
    for i in range(0, 2048, 4):
        init_snippets.append("INIT[%4d*8 +: 8]" % (i))
        init_snippets.append("1'b0")
        init_snippets.append("INIT[%4d*8 +: 8]" % (i+1))
        init_snippets.append("1'b0")
    #init_snippets = list(reversed(init_snippets))
    for i in range(2, 2049, 4):
        init_snippets.append("INIT[%4d*8 +: 8]" % (i))
        init_snippets.append("1'b0")
        init_snippets.append("INIT[%4d*8 +: 8]" % (i+1))
        init_snippets.append("1'b0")
    init_snippets = list(reversed(init_snippets))
    for k in range(8, 4096, 8):
        init_snippets[k] = "\n          " + init_snippets[k]
    print(".INIT({%s})," % (", ".join(init_snippets)), file=f)
