blockram_template = """\
design -reset; read_verilog -defer ../../common/blockram.v
chparam -set ADDRESS_WIDTH {aw} -set DATA_WIDTH {dw} {top}
hierarchy -top {top}
synth_quicklogic -family qlf_k6n10f -top {top}; cd {top}
log TESTING aw:{aw} dw:{dw} top:{top}\
"""
blockram_tests: "list[tuple[int, int, str, list[str]]]" = [
    # TDP36K = 1024x36bit RAM, 2048x18bit or 4096x9bit also work
    (10, 36, "sync_ram_*dp",     ["-assert-count 1 t:TDP36K"]),
    (11, 18, "sync_ram_*dp",     ["-assert-count 1 t:TDP36K"]),
    (12,  9, "sync_ram_*dp",     ["-assert-count 1 t:TDP36K"]),
    # larger sizes need an extra ram
    (10, 48, "sync_ram_*dp",     ["-assert-count 2 t:TDP36K"]),
    (11, 36, "sync_ram_*dp",     ["-assert-count 2 t:TDP36K"]),
    (12, 18, "sync_ram_*dp",     ["-assert-count 2 t:TDP36K"]),
    (12, 10, "sync_ram_*dp",     ["-assert-count 2 t:TDP36K"]),
    # 4096x20bit *can* fit in 3, albeit somewhat awkwardly
    (12, 20, "sync_ram_*dp",     ["-assert-min 3 t:TDP36K",
                                  "-assert-max 4 t:TDP36K"]),
    # smaller sizes can still fit in one
    (10, 32, "sync_ram_*dp",     ["-assert-count 1 t:TDP36K"]),
    (10, 18, "sync_ram_*dp",     ["-assert-count 1 t:TDP36K"]),
    (10,  9, "sync_ram_*dp",     ["-assert-count 1 t:TDP36K"]),
    (11, 16, "sync_ram_*dp",     ["-assert-count 1 t:TDP36K"]),
    (11,  9, "sync_ram_*dp",     ["-assert-count 1 t:TDP36K"]),
    (12,  8, "sync_ram_*dp",     ["-assert-count 1 t:TDP36K"]),
    (13,  4, "sync_ram_*dp",     ["-assert-count 1 t:TDP36K"]),
    (14,  2, "sync_ram_*dp",     ["-assert-count 1 t:TDP36K"]),
    (15,  1, "sync_ram_*dp",     ["-assert-count 1 t:TDP36K"]),
    # 2x write width (1024x36bit write / 2048x18bit read = 1TDP36K)
    (11, 18, "sync_ram_sdp_wwr", ["-assert-count 1 t:TDP36K"]),
    (11,  9, "sync_ram_sdp_wwr", ["-assert-count 1 t:TDP36K"]),
    # 2x read width (1024x36bit read / 2048x18bit write = 1TDP36K)
    (11, 18, "sync_ram_sdp_wrr", ["-assert-count 1 t:TDP36K"]),
    (10, 36, "sync_ram_sdp_wrr", ["-assert-count 1 t:TDP36K"]),
]

with open("t_mem.ys", mode="w") as f:
    for (aw, dw, top, assertions) in blockram_tests:
        if "*" in top:
            star_sub = ["s", "t"]
        else:
            star_sub = [""]
        for sub in star_sub:
            print(
                blockram_template.format(aw=aw, dw=dw, top=top.replace("*", sub)),
                file=f
            )
            for assertion in assertions:
                print("select {}\n".format(assertion), file=f, end=None)
