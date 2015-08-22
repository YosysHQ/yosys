#!/usr/bin/env python3

def write_init_vh(filename, initbits):
    with open(filename, "w") as f:
        for i in range(16):
            print("localparam [255:0] INIT_%X = {" % i, file=f)
            for k in range(32):
                print("  %s%s" % (", ".join(["INIT[%4d]" % initbits[i*256 + 255 - k*8 - l] for l in range(8)]), "," if k != 31 else ""), file=f)
            print("};", file=f);

write_init_vh("techlibs/ice40/brams_init1.vh", [i//2 + 2048*(i%2) for i in range(4096)])
write_init_vh("techlibs/ice40/brams_init2.vh", [i//4 + 1024*(i%4) for i in range(4096)])
write_init_vh("techlibs/ice40/brams_init3.vh", [i//8 +  512*(i%8) for i in range(4096)])

