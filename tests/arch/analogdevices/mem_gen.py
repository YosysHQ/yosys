from __future__ import annotations

from dataclasses import dataclass


blockram_template = """# ======================================
log ** GENERATING TEST {top} WITH PARAMS{param_str}
design -reset; read_verilog -defer ../common/blockram.v
chparam{param_str} {top}
hierarchy -top {top}
echo on
debug synth_analogdevices -tech {tech} -top {top} {opts} -run :map_ffram
stat; echo off
"""
inference_tests: "list[tuple[str, list[tuple[str, int]], str, list[str], list[str]]]" = [
    # RBRAM2 has TDP and SDP for 8192x5bit, 4096x9bit, and 2048x40bit
    ("t16ffc", [("ADDRESS_WIDTH", 13), ("DATA_WIDTH", 5)], "sync_ram_*dp", ["-assert-count 1 t:RBRAM2"], []),
    ("t16ffc", [("ADDRESS_WIDTH", 12), ("DATA_WIDTH", 9)], "sync_ram_*dp", ["-assert-count 1 t:RBRAM2"], []),
    ("t16ffc", [("ADDRESS_WIDTH", 11), ("DATA_WIDTH", 40)], "sync_ram_*dp", ["-assert-count 1 t:RBRAM2"], []),
    # LUTRAM is generally cheaper than BRAM for undersized (SDP) memories
    ("t16ffc", [("ADDRESS_WIDTH", 6), ("DATA_WIDTH", 1)], "sync_ram_sdp", ["-assert-count 1 t:RAMD64X1"], []),
    ("t16ffc", [("ADDRESS_WIDTH", 6), ("DATA_WIDTH", 8)], "sync_ram_sdp", ["-assert-count 8 t:RAMD64X1"], []),
    ("t16ffc", [("ADDRESS_WIDTH", 10), ("DATA_WIDTH", 8)], "sync_ram_sdp", ["-assert-count 128 t:RAMD64X1"], []),
    ("t16ffc", [("ADDRESS_WIDTH", 10), ("DATA_WIDTH", 16)], "sync_ram_sdp", ["-assert-count 256 t:RAMD64X1"], []),
    # RBRAM is half the depth of RBRAM2, and doesn't have TDP, also LUTRAM is cheaper, so we need to specify not to use it
    ("t40lp", [("ADDRESS_WIDTH", 13), ("DATA_WIDTH", 5)], "sync_ram_sdp", ["-assert-count 2 t:RBRAM"], ["-nolutram"]),
    ("t40lp", [("ADDRESS_WIDTH", 12), ("DATA_WIDTH", 5)], "sync_ram_sdp", ["-assert-count 1 t:RBRAM"], ["-nolutram"]),
    ("t40lp", [("ADDRESS_WIDTH", 11), ("DATA_WIDTH", 9)], "sync_ram_sdp", ["-assert-count 1 t:RBRAM"], ["-nolutram"]),
    ("t40lp", [("ADDRESS_WIDTH", 10), ("DATA_WIDTH", 40)], "sync_ram_sdp", ["-assert-count 1 t:RBRAM"], ["-nolutram"]),
    # 2048x32 and 2048x36bit are also valid
    ("t16ffc", [("ADDRESS_WIDTH", 11), ("DATA_WIDTH", 32)], "sync_ram_*dp", ["-assert-count 1 t:RBRAM2"], []),
    ("t16ffc", [("ADDRESS_WIDTH", 11), ("DATA_WIDTH", 36)], "sync_ram_*dp", ["-assert-count 1 t:RBRAM2"], []),
    ("t40lp", [("ADDRESS_WIDTH", 10), ("DATA_WIDTH", 32)], "sync_ram_sdp", ["-assert-count 1 t:RBRAM"], ["-nolutram"]),
    ("t40lp", [("ADDRESS_WIDTH", 10), ("DATA_WIDTH", 36)], "sync_ram_sdp", ["-assert-count 1 t:RBRAM"], ["-nolutram"]),

    # 4096x16/18bit can be mapped to a single 2048x32/36bit
    ("t16ffc", [("ADDRESS_WIDTH", 12), ("DATA_WIDTH", 16)], "sync_ram_*dp", ["-assert-count 1 t:RBRAM2"], []),
    ("t16ffc", [("ADDRESS_WIDTH", 12), ("DATA_WIDTH", 18)], "sync_ram_*dp", ["-assert-count 1 t:RBRAM2"], []),
    ("t40lp", [("ADDRESS_WIDTH", 11), ("DATA_WIDTH", 16)], "sync_ram_sdp", ["-assert-count 1 t:RBRAM"], ["-nolutram"]),
    ("t40lp", [("ADDRESS_WIDTH", 11), ("DATA_WIDTH", 18)], "sync_ram_sdp", ["-assert-count 1 t:RBRAM"], ["-nolutram"]),
    # same for 8192x8/9bit
    ("t16ffc", [("ADDRESS_WIDTH", 13), ("DATA_WIDTH", 8)], "sync_ram_*dp", ["-assert-count 1 t:RBRAM2"], []),
    ("t16ffc", [("ADDRESS_WIDTH", 13), ("DATA_WIDTH", 9)], "sync_ram_*dp", ["-assert-count 1 t:RBRAM2"], []),
    ("t40lp", [("ADDRESS_WIDTH", 12), ("DATA_WIDTH", 8)], "sync_ram_sdp", ["-assert-count 1 t:RBRAM"], ["-nolutram"]),
    ("t40lp", [("ADDRESS_WIDTH", 12), ("DATA_WIDTH", 9)], "sync_ram_sdp", ["-assert-count 1 t:RBRAM"], ["-nolutram"]),
    # but 4096x20bit requires extra memories because 2048x40bit has 8bit byte enables (which doesn't divide 20bit evenly)
    ("t16ffc", [("ADDRESS_WIDTH", 12), ("DATA_WIDTH", 20)], "sync_ram_sdp", ["-assert-count 2 t:RBRAM2"], []),
    ("t40lp", [("ADDRESS_WIDTH", 11), ("DATA_WIDTH", 20)], "sync_ram_sdp", ["-assert-count 2 t:RBRAM"], ["-nolutram"]),
]

@dataclass
class TestClass:
    params: dict[str, int]
    top: str
    assertions: list[str]
    test_steps: None | list[dict[str, int]]
    opts: list[str]
    tech: str = "t16ffc"

sim_tests: list[TestClass] = []

for (tech, params, top, assertions, opts) in inference_tests:
    sim_test = TestClass(
        params=dict(params),
        top=top,
        assertions=assertions,
        test_steps=None,
        opts=opts,
        tech=tech,
    )
    sim_tests.append(sim_test)

i = 0
j = 0
max_j = 16
f = None
for sim_test in sim_tests:
    # format params
    param_str = ""
    for (key, val) in sim_test.params.items():
        param_str += f" -set {key} {val}"

    # resolve top module wildcards
    top_list = [sim_test.top]
    if "*dp" in sim_test.top:
        top_list += [
            sim_test.top.replace("*dp", dp_sub) for dp_sub in ["sdp", "tdp"]
        ]
    if "w*r" in sim_test.top:
        top_list += [
            sim_test.top.replace("w*r", wr_sub) for wr_sub in ["wwr", "wrr"]
        ]
    if len(top_list) > 1:
        top_list.pop(0)

    # iterate over string substitutions
    for top in top_list:
        # limit number of tests per file to allow parallel make
        if not f:
            fn = f"t_mem{i}.ys"
            f = open(fn, mode="w")
            j = 0

        # output yosys script test file
        print(
            blockram_template.format(param_str=param_str, top=top, tech=sim_test.tech, opts=" ".join(sim_test.opts)),
            file=f
        )
        for assertion in sim_test.assertions:
            print(f"log ** CHECKING CELL COUNTS FOR TEST {top} WITH PARAMS{param_str} ON TECH {sim_test.tech}", file=f)
            print(f"select {assertion}", file=f)
        print("", file=f)

        # increment test counter
        j += 1
        if j >= max_j:
            f = f.close()
            i += 1

if f:
    f.close()
