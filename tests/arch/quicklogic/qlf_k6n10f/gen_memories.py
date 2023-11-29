blockram_template = """# ======================================
design -reset; read_verilog -defer ../../common/blockram.v
chparam{param_str} {top}
hierarchy -top {top}
synth_quicklogic -family qlf_k6n10f -top {top}; cd {top}
log ** TESTING {top} WITH PARAMS{param_str}\
"""
blockram_tests: "list[tuple[list[tuple[str, int]], str, list[str]]]" = [
    # TDP36K = 1024x36bit RAM, 2048x18bit or 4096x9bit also work
    ([("ADDRESS_WIDTH", 10), ("DATA_WIDTH", 36)], "sync_ram_*dp", ["-assert-count 1 t:TDP36K"]),
    ([("ADDRESS_WIDTH", 11), ("DATA_WIDTH", 18)], "sync_ram_*dp", ["-assert-count 1 t:TDP36K"]),
    ([("ADDRESS_WIDTH", 12), ("DATA_WIDTH",  9)], "sync_ram_*dp", ["-assert-count 1 t:TDP36K"]),
    # larger sizes need an extra ram
    ([("ADDRESS_WIDTH", 10), ("DATA_WIDTH", 48)], "sync_ram_*dp", ["-assert-count 2 t:TDP36K"]),
    ([("ADDRESS_WIDTH", 11), ("DATA_WIDTH", 36)], "sync_ram_*dp", ["-assert-count 2 t:TDP36K"]),
    ([("ADDRESS_WIDTH", 12), ("DATA_WIDTH", 18)], "sync_ram_*dp", ["-assert-count 2 t:TDP36K"]),
    ([("ADDRESS_WIDTH", 12), ("DATA_WIDTH", 10)], "sync_ram_*dp", ["-assert-count 2 t:TDP36K"]),
    # 4096x20bit *can* fit in 3, albeit somewhat awkwardly
    ([("ADDRESS_WIDTH", 12), ("DATA_WIDTH", 20)], "sync_ram_*dp", ["-assert-min 3 t:TDP36K",
                                                                   "-assert-max 4 t:TDP36K"]),

    # smaller sizes can still fit in one, and assign the correct width (1, 2, 4, 8, 18 or 36)
    ([("ADDRESS_WIDTH", 10), ("DATA_WIDTH", 32)], "sync_ram_*dp", ["-assert-count 1 t:TDP36K", "-assert-count 1 t:TDP36K a:port_a_width=36 %i"]),
    ([("ADDRESS_WIDTH", 10), ("DATA_WIDTH", 24)], "sync_ram_*dp", ["-assert-count 1 t:TDP36K", "-assert-count 1 t:TDP36K a:port_a_width=36 %i"]),
    ([("ADDRESS_WIDTH", 10), ("DATA_WIDTH", 18)], "sync_ram_*dp", ["-assert-count 1 t:TDP36K", "-assert-count 1 t:TDP36K a:port_a_width=18 %i"]),
    ([("ADDRESS_WIDTH", 10), ("DATA_WIDTH",  9)], "sync_ram_*dp", ["-assert-count 1 t:TDP36K", "-assert-count 1 t:TDP36K a:port_a_width=9 %i"]),
    ([("ADDRESS_WIDTH", 11), ("DATA_WIDTH", 16)], "sync_ram_*dp", ["-assert-count 1 t:TDP36K", "-assert-count 1 t:TDP36K a:port_a_width=18 %i"]),
    ([("ADDRESS_WIDTH", 11), ("DATA_WIDTH",  9)], "sync_ram_*dp", ["-assert-count 1 t:TDP36K", "-assert-count 1 t:TDP36K a:port_a_width=9 %i"]),
    ([("ADDRESS_WIDTH", 12), ("DATA_WIDTH",  8)], "sync_ram_*dp", ["-assert-count 1 t:TDP36K", "-assert-count 1 t:TDP36K a:port_a_width=9 %i"]),
    ([("ADDRESS_WIDTH", 13), ("DATA_WIDTH",  4)], "sync_ram_*dp", ["-assert-count 1 t:TDP36K", "-assert-count 1 t:TDP36K a:port_a_width=4 %i"]),
    ([("ADDRESS_WIDTH", 14), ("DATA_WIDTH",  2)], "sync_ram_*dp", ["-assert-count 1 t:TDP36K", "-assert-count 1 t:TDP36K a:port_a_width=2 %i"]),
    ([("ADDRESS_WIDTH", 15), ("DATA_WIDTH",  1)], "sync_ram_*dp", ["-assert-count 1 t:TDP36K", "-assert-count 1 t:TDP36K a:port_a_width=1 %i"]),

    # 2x write width (1024x36bit write / 2048x18bit read = 1TDP36K)
    ([("ADDRESS_WIDTH", 11), ("DATA_WIDTH", 18), ("WRITE_SHIFT", 1)], "sync_ram_sdp_wwr", ["-assert-count 1 t:TDP36K"]),
    ([("ADDRESS_WIDTH", 11), ("DATA_WIDTH", 16), ("WRITE_SHIFT", 1)], "sync_ram_sdp_wwr", ["-assert-count 1 t:TDP36K"]),
    ([("ADDRESS_WIDTH", 12), ("DATA_WIDTH",  9), ("WRITE_SHIFT", 1)], "sync_ram_sdp_wwr", ["-assert-count 1 t:TDP36K"]),
    ([("ADDRESS_WIDTH", 12), ("DATA_WIDTH",  8), ("WRITE_SHIFT", 1)], "sync_ram_sdp_wwr", ["-assert-count 1 t:TDP36K"]),
    # same for read
    ([("ADDRESS_WIDTH", 11), ("DATA_WIDTH", 18), ( "READ_SHIFT", 1)], "sync_ram_sdp_wrr", ["-assert-count 1 t:TDP36K"]),
    ([("ADDRESS_WIDTH", 11), ("DATA_WIDTH", 16), ( "READ_SHIFT", 1)], "sync_ram_sdp_wrr", ["-assert-count 1 t:TDP36K"]),
    ([("ADDRESS_WIDTH", 12), ("DATA_WIDTH",  9), ( "READ_SHIFT", 1)], "sync_ram_sdp_wrr", ["-assert-count 1 t:TDP36K"]),
    ([("ADDRESS_WIDTH", 12), ("DATA_WIDTH",  8), ( "READ_SHIFT", 1)], "sync_ram_sdp_wrr", ["-assert-count 1 t:TDP36K"]),

    # 4x write width (1024x36bit write / 4096x9bit read = 1TDP36K)
    ([("ADDRESS_WIDTH", 11), ("DATA_WIDTH",  4), ("WRITE_SHIFT", 2)], "sync_ram_sdp_wwr", ["-assert-count 1 t:TDP36K"]),
    ([("ADDRESS_WIDTH", 12), ("DATA_WIDTH",  9), ("WRITE_SHIFT", 2)], "sync_ram_sdp_wwr", ["-assert-count 1 t:TDP36K"]),
    ([("ADDRESS_WIDTH", 12), ("DATA_WIDTH",  8), ("WRITE_SHIFT", 2)], "sync_ram_sdp_wwr", ["-assert-count 1 t:TDP36K"]),
    # and again for read
    ([("ADDRESS_WIDTH", 11), ("DATA_WIDTH",  4), ( "READ_SHIFT", 2)], "sync_ram_sdp_wrr", ["-assert-count 1 t:TDP36K"]),
    ([("ADDRESS_WIDTH", 12), ("DATA_WIDTH",  9), ( "READ_SHIFT", 2)], "sync_ram_sdp_wrr", ["-assert-count 1 t:TDP36K"]),
    ([("ADDRESS_WIDTH", 12), ("DATA_WIDTH",  8), ( "READ_SHIFT", 2)], "sync_ram_sdp_wrr", ["-assert-count 1 t:TDP36K"]),

    # etc
    ([("ADDRESS_WIDTH", 11), ("DATA_WIDTH", 16), ("WRITE_SHIFT", 1)], "sync_ram_sdp_wwr", ["-assert-count 1 t:TDP36K"]),
    ([("ADDRESS_WIDTH", 11), ("DATA_WIDTH", 16), ( "READ_SHIFT", 1)], "sync_ram_sdp_wrr", ["-assert-count 1 t:TDP36K"]),
    ([("ADDRESS_WIDTH", 12), ("DATA_WIDTH",  8), ("WRITE_SHIFT", 2)], "sync_ram_sdp_wwr", ["-assert-count 1 t:TDP36K"]),
    ([("ADDRESS_WIDTH", 12), ("DATA_WIDTH",  8), ( "READ_SHIFT", 2)], "sync_ram_sdp_wrr", ["-assert-count 1 t:TDP36K"]),

    # can also use an extra TDP36K for higher width
    ([("ADDRESS_WIDTH", 10), ("DATA_WIDTH", 36), ("WRITE_SHIFT", 1)], "sync_ram_sdp_wwr", ["-assert-count 2 t:TDP36K"]),
    ([("ADDRESS_WIDTH", 10), ("DATA_WIDTH", 36), ( "READ_SHIFT", 1)], "sync_ram_sdp_wrr", ["-assert-count 2 t:TDP36K"]),

    # not sure why these are different but apparently wide writes pack better?
    ([("ADDRESS_WIDTH", 10), ("DATA_WIDTH", 36), ("WRITE_SHIFT", 2)], "sync_ram_sdp_wwr", ["-assert-count 2 t:TDP36K"]),
    ([("ADDRESS_WIDTH", 10), ("DATA_WIDTH", 36), ( "READ_SHIFT", 2)], "sync_ram_sdp_wrr", ["-assert-count 4 t:TDP36K"]),
    ([("ADDRESS_WIDTH",  9), ("DATA_WIDTH", 36), ("WRITE_SHIFT", 2)], "sync_ram_sdp_wwr", ["-assert-count 2 t:TDP36K"]),
    ([("ADDRESS_WIDTH",  9), ("DATA_WIDTH", 36), ( "READ_SHIFT", 2)], "sync_ram_sdp_wrr", ["-assert-count 4 t:TDP36K"]),

    # SHIFT=0 should be identical to sync_ram_sdp
    ([("ADDRESS_WIDTH", 10), ("DATA_WIDTH", 36), ( "READ_SHIFT", 0)], "sync_ram_sdp_wrr", ["-assert-count 1 t:TDP36K"]),
    ([("ADDRESS_WIDTH", 11), ("DATA_WIDTH", 18), ( "READ_SHIFT", 0)], "sync_ram_sdp_wrr", ["-assert-count 1 t:TDP36K"]),
    # but WRITE_SHIFT=0 doesn't generate any read circuitry and optimises the memory away
#   ([("ADDRESS_WIDTH", 10), ("DATA_WIDTH", 36), ("WRITE_SHIFT", 0)], "sync_ram_sdp_wwr", ["-assert-count 1 t:TDP36K"]),
#   ([("ADDRESS_WIDTH", 11), ("DATA_WIDTH", 18), ("WRITE_SHIFT", 0)], "sync_ram_sdp_wwr", ["-assert-count 1 t:TDP36K"]),

    # two disjoint 18K memories can share a single TDP36K
    ([("ADDRESS_WIDTH_A", 10), ("DATA_WIDTH_A", 18),
      ("ADDRESS_WIDTH_B", 10), ("DATA_WIDTH_B", 18)], "double_sync_ram_sdp", ["-assert-count 1 t:TDP36K"]),
    ([("ADDRESS_WIDTH_A", 10), ("DATA_WIDTH_A", 16),
      ("ADDRESS_WIDTH_B", 11), ("DATA_WIDTH_B",  8)], "double_sync_ram_sdp", ["-assert-count 1 t:TDP36K"]),
    ([("ADDRESS_WIDTH_A", 14), ("DATA_WIDTH_A",  1),
      ("ADDRESS_WIDTH_B", 11), ("DATA_WIDTH_B",  8)], "double_sync_ram_sdp", ["-assert-count 1 t:TDP36K"]),
    # but only if data width is <= 18
    ([("ADDRESS_WIDTH_A",  9), ("DATA_WIDTH_A", 36),
      ("ADDRESS_WIDTH_B", 11), ("DATA_WIDTH_B",  9)], "double_sync_ram_sdp", ["-assert-count 2 t:TDP36K"]),
    # sharing a TDP36K sets is_split=1
    ([("ADDRESS_WIDTH_A", 10), ("DATA_WIDTH_A", 18),
      ("ADDRESS_WIDTH_B", 10), ("DATA_WIDTH_B", 18)], "double_sync_ram_sdp", ["-assert-count 1 t:TDP36K a:is_split=1 %i"]),
    # an unshared TDP36K sets is_split=0
    ([("ADDRESS_WIDTH", 10), ("DATA_WIDTH", 36)],     "sync_ram_*dp",        ["-assert-count 1 t:TDP36K a:is_split=0 %i"]),
]

with open("t_mem.ys", mode="w") as f:
    for (params, top, assertions) in blockram_tests:
        param_str = ""
        for (key, val) in params:
            param_str += f" -set {key} {val}"
        if "*" in top:
            star_sub = ["s", "t"]
        else:
            star_sub = [""]
        for sub in star_sub:
            print(
                blockram_template.format(param_str=param_str, top=top.replace("*", sub)),
                file=f
            )
            for assertion in assertions:
                print("select {}".format(assertion), file=f)
            print("", file=f)
