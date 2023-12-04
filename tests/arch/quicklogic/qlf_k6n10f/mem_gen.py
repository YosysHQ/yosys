from __future__ import annotations

from dataclasses import dataclass


blockram_template = """# ======================================
log ** GENERATING TEST {top} WITH PARAMS{param_str}
design -reset; read_verilog -defer ../../common/blockram.v
chparam{param_str} {top}
hierarchy -top {top}
synth_quicklogic -family qlf_k6n10f -top {top}
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

    # 2x asymmetric (1024x36bit write / 2048x18bit read or vice versa = 1TDP36K) 
    ([("ADDRESS_WIDTH", 11), ("DATA_WIDTH", 18), ("SHIFT_VAL", 1)], "sync_ram_sdp_w*r", ["-assert-count 1 t:TDP36K"]),
    ([("ADDRESS_WIDTH", 11), ("DATA_WIDTH", 16), ("SHIFT_VAL", 1)], "sync_ram_sdp_w*r", ["-assert-count 1 t:TDP36K"]),
    ([("ADDRESS_WIDTH", 12), ("DATA_WIDTH",  9), ("SHIFT_VAL", 1)], "sync_ram_sdp_w*r", ["-assert-count 1 t:TDP36K"]),
    ([("ADDRESS_WIDTH", 12), ("DATA_WIDTH",  8), ("SHIFT_VAL", 1)], "sync_ram_sdp_w*r", ["-assert-count 1 t:TDP36K"]),

    # 4x asymmetric (1024x36bit write / 4096x9bit read or vice versa = 1TDP36K)
    ([("ADDRESS_WIDTH", 11), ("DATA_WIDTH",  4), ("SHIFT_VAL", 2)], "sync_ram_sdp_w*r", ["-assert-count 1 t:TDP36K"]),
    ([("ADDRESS_WIDTH", 12), ("DATA_WIDTH",  9), ("SHIFT_VAL", 2)], "sync_ram_sdp_w*r", ["-assert-count 1 t:TDP36K"]),
    ([("ADDRESS_WIDTH", 12), ("DATA_WIDTH",  8), ("SHIFT_VAL", 2)], "sync_ram_sdp_w*r", ["-assert-count 1 t:TDP36K"]),

    # can also use an extra TDP36K for higher width
    ([("ADDRESS_WIDTH", 11), ("DATA_WIDTH", 16), ("SHIFT_VAL", 1)], "sync_ram_sdp_w*r", ["-assert-count 1 t:TDP36K"]),
    ([("ADDRESS_WIDTH", 12), ("DATA_WIDTH",  8), ("SHIFT_VAL", 2)], "sync_ram_sdp_w*r", ["-assert-count 1 t:TDP36K"]),
    ([("ADDRESS_WIDTH", 10), ("DATA_WIDTH", 36), ("SHIFT_VAL", 1)], "sync_ram_sdp_w*r", ["-assert-count 2 t:TDP36K"]),
    ([("ADDRESS_WIDTH", 10), ("DATA_WIDTH", 36), ("SHIFT_VAL", 2)], "sync_ram_sdp_w*r", ["-assert-count 4 t:TDP36K"]),
    ([("ADDRESS_WIDTH",  9), ("DATA_WIDTH", 36), ("SHIFT_VAL", 2)], "sync_ram_sdp_w*r", ["-assert-count 4 t:TDP36K"]),

    # # SHIFT=0 should be identical to sync_ram_sdp
    ([("ADDRESS_WIDTH", 10), ("DATA_WIDTH", 36), ("SHIFT_VAL", 0)], "sync_ram_sdp_w*r", ["-assert-count 1 t:TDP36K"]),
    ([("ADDRESS_WIDTH", 11), ("DATA_WIDTH", 18), ("SHIFT_VAL", 0)], "sync_ram_sdp_w*r", ["-assert-count 1 t:TDP36K"]),

    # asymmetric memories assign different port widths on a and b ports
    ([("ADDRESS_WIDTH", 10), ("DATA_WIDTH", 18), ("SHIFT_VAL", 1)], "sync_ram_sdp_wwr", ["-assert-count 1 t:TDP36K", "-assert-count 1 t:TDP36K a:port_a_width=36 %i a:port_b_width=18 %i"]),
    ([("ADDRESS_WIDTH", 10), ("DATA_WIDTH",  9), ("SHIFT_VAL", 1)], "sync_ram_sdp_wwr", ["-assert-count 1 t:TDP36K", "-assert-count 1 t:TDP36K a:port_a_width=18 %i a:port_b_width=9  %i"]),
    ([("ADDRESS_WIDTH", 10), ("DATA_WIDTH",  9), ("SHIFT_VAL", 2)], "sync_ram_sdp_wwr", ["-assert-count 1 t:TDP36K", "-assert-count 1 t:TDP36K a:port_a_width=36 %i a:port_b_width=9  %i"]),
    ([("ADDRESS_WIDTH", 10), ("DATA_WIDTH", 18), ("SHIFT_VAL", 1)], "sync_ram_sdp_wrr", ["-assert-count 1 t:TDP36K", "-assert-count 1 t:TDP36K a:port_a_width=18 %i a:port_b_width=36 %i"]),
    ([("ADDRESS_WIDTH", 10), ("DATA_WIDTH",  9), ("SHIFT_VAL", 1)], "sync_ram_sdp_wrr", ["-assert-count 1 t:TDP36K", "-assert-count 1 t:TDP36K a:port_a_width=9  %i a:port_b_width=18 %i"]),
    ([("ADDRESS_WIDTH", 10), ("DATA_WIDTH",  9), ("SHIFT_VAL", 2)], "sync_ram_sdp_wrr", ["-assert-count 1 t:TDP36K", "-assert-count 1 t:TDP36K a:port_a_width=9  %i a:port_b_width=36 %i"]),

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

    # also for tdp
    ([("ADDRESS_WIDTH", 10), ("DATA_WIDTH", 18)], "double_sync_ram_tdp", ["-assert-count 1 t:TDP36K"]),
    ([("ADDRESS_WIDTH", 10), ("DATA_WIDTH", 16)], "double_sync_ram_tdp", ["-assert-count 1 t:TDP36K"]),
    ([("ADDRESS_WIDTH", 11), ("DATA_WIDTH",  8)], "double_sync_ram_tdp", ["-assert-count 1 t:TDP36K"]),
    ([("ADDRESS_WIDTH", 12), ("DATA_WIDTH",  4)], "double_sync_ram_tdp", ["-assert-count 1 t:TDP36K"]),
    ([("ADDRESS_WIDTH", 13), ("DATA_WIDTH",  2)], "double_sync_ram_tdp", ["-assert-count 1 t:TDP36K"]),
    ([("ADDRESS_WIDTH", 14), ("DATA_WIDTH",  1)], "double_sync_ram_tdp", ["-assert-count 1 t:TDP36K"]),
    # still only if data width is <= 18
    ([("ADDRESS_WIDTH",  9), ("DATA_WIDTH", 36)], "double_sync_ram_tdp", ["-assert-count 2 t:TDP36K"]),

    # sharing a TDP36K sets is_split=1
    ([("ADDRESS_WIDTH_A", 10), ("DATA_WIDTH_A", 18),
      ("ADDRESS_WIDTH_B", 10), ("DATA_WIDTH_B", 18)], "double_sync_ram_sdp", ["-assert-count 1 t:TDP36K a:is_split=1 %i"]),
    ([("ADDRESS_WIDTH", 10), ("DATA_WIDTH", 18)],     "double_sync_ram_tdp", ["-assert-count 1 t:TDP36K a:is_split=1 %i"]),
    # an unshared TDP36K sets is_split=0
    ([("ADDRESS_WIDTH", 10), ("DATA_WIDTH", 36)],     "sync_ram_*dp",        ["-assert-count 1 t:TDP36K a:is_split=0 %i"]),
    ([("ADDRESS_WIDTH", 11), ("DATA_WIDTH", 18)],     "sync_ram_sdp_w*r",    ["-assert-count 1 t:TDP36K a:is_split=0 %i"]),

    # sharing a TDP36K sets correct port widths
    ([("ADDRESS_WIDTH_A", 10), ("DATA_WIDTH_A", 18), ("DATA_WIDTH_B", 18), ("ADDRESS_WIDTH_B", 10)], "double_sync_ram_sdp",
     ["-assert-count 1 t:TDP36K a:port_a1_width=18 %i a:port_a2_width=18 %i",
      "-assert-count 1 t:TDP36K"]),
    ([("ADDRESS_WIDTH", 10), ("DATA_WIDTH", 18)],                                                    "double_sync_ram_tdp",
     ["-assert-count 1 t:TDP36K a:port_a1_width=18 %i a:port_a2_width=18 %i",
      "-assert-count 1 t:TDP36K"]),
    ([("ADDRESS_WIDTH_A", 10), ("DATA_WIDTH_A", 16), ("DATA_WIDTH_B", 8),  ("ADDRESS_WIDTH_B", 11)], "double_sync_ram_sdp",
     ["-assert-count 1 t:TDP36K a:port_a1_width=18 %i a:port_a2_width=9  %i "
                    + "t:TDP36K a:port_a2_width=18 %i a:port_a1_width=9  %i %u",
      "-assert-count 1 t:TDP36K"]),
    ([("ADDRESS_WIDTH_A", 12), ("DATA_WIDTH_A", 4),  ("DATA_WIDTH_B", 12), ("ADDRESS_WIDTH_B", 10)], "double_sync_ram_sdp",
     ["-assert-count 1 t:TDP36K a:port_a1_width=4  %i a:port_a2_width=18 %i "
                    + "t:TDP36K a:port_a2_width=4  %i a:port_a1_width=18 %i %u",
      "-assert-count 1 t:TDP36K"]),
    ([("ADDRESS_WIDTH_A", 13), ("DATA_WIDTH_A", 2),  ("DATA_WIDTH_B", 1),  ("ADDRESS_WIDTH_B", 14)], "double_sync_ram_sdp",
     ["-assert-count 1 t:TDP36K a:port_a1_width=2  %i a:port_a2_width=1  %i "
                    + "t:TDP36K a:port_a2_width=2  %i a:port_a1_width=1  %i %u",
      "-assert-count 1 t:TDP36K"]),
]

sim_template = """\
design -stash synthesized
design -copy-from synthesized -as {top}_synth {top}
design -delete synthesized
read_verilog +/quicklogic/common/cells_sim.v +/quicklogic/qlf_k6n10f/cells_sim.v +/quicklogic/qlf_k6n10f/brams_sim.v +/quicklogic/qlf_k6n10f/sram1024x18_mem.v +/quicklogic/qlf_k6n10f/ufifo_ctl.v +/quicklogic/qlf_k6n10f/TDP18K_FIFO.v
read_verilog <<EOF
`define MEM_TEST_VECTOR {mem_test_vector}

`define UUT_SUBMODULE \\
{uut_submodule}
EOF
read_verilog -defer -formal mem_tb.v
chparam{param_str} -set VECTORLEN {vectorlen} TB
hierarchy -top TB -check
prep
log ** CHECKING SIMULATION FOR TEST {top} WITH PARAMS{param_str}
sim -clock clk -n {vectorlen} -assert
"""

sync_ram_sdp_submodule = """\
sync_ram_sdp_synth uut (\\
	.clk(clk),\\
	.address_in_r(ra_a),\\
	.data_out(rq_a),\\
	.write_enable(wce_a),\\
	.address_in_w(wa_a),\\
	.data_in(wd_a)\\
);\
"""

sync_ram_tdp_submodule = """\
sync_ram_tdp_synth uut (\\
	.clk_a(clk),\\
	.clk_b(clk),\\
	.write_enable_a(wce_a),\\
	.write_enable_b(wce_b),\\
	.read_enable_a(rce_a),\\
	.read_enable_b(rce_b),\\
	.addr_a(ra_a),\\
	.addr_b(ra_b),\\
	.read_data_a(rq_a),\\
	.read_data_b(rq_b),\\
	.write_data_a(wd_a),\\
	.write_data_b(wd_b)\\
);\
"""

sync_ram_sdp_wwr_submodule = """\
sync_ram_sdp_wwr_synth uut (\\
	.clk_w(clk),\\
	.clk_r(clk),\\
	.write_enable(wce_a),\\
	.data_in(wd_a),\\
	.address_in_w(wa_a),\\
	.address_in_r(ra_a),\\
	.data_out(rq_a)\\
);\
"""

sync_ram_sdp_wrr_submodule = """\
sync_ram_sdp_wrr_synth uut (\\
	.clk_w(clk),\\
	.clk_r(clk),\\
	.write_enable(wce_a),\\
	.data_in(wd_a),\\
	.address_in_w(wa_a),\\
	.address_in_r(ra_a),\\
	.data_out(rq_a)\\
);\
"""

double_sync_ram_sdp_submodule = """\
double_sync_ram_sdp_synth uut (\\
	.clk_a(clk),\\
	.write_enable_a(wce_a),\\
	.address_in_w_a(wa_a),\\
	.address_in_r_a(ra_a),\\
	.data_in_a(wd_a),\\
	.data_out_a(rq_a),\\
	.clk_b(clk),\\
	.write_enable_b(wce_b),\\
	.address_in_w_b(wa_b),\\
	.address_in_r_b(ra_b),\\
	.data_in_b(wd_b),\\
	.data_out_b(rq_b)\\
);\
"""

@dataclass
class TestClass:
    params: dict[str, int]
    top: str
    assertions: list[str]
    test_steps: None | list[dict[str, int]]

test_val_map = {
    "rce_a": "rce_a_testvector",
    "ra_a":  "ra_a_testvector",
    "rq_a":  "rq_a_expected",
    "wce_a": "wce_a_testvector",
    "wa_a":  "wa_a_testvector",
    "wd_a":  "wd_a_testvector",
    "rce_b": "rce_b_testvector",
    "ra_b":  "ra_b_testvector",
    "rq_b":  "rq_b_expected",
    "wce_b": "wce_b_testvector",
    "wa_b":  "wa_b_testvector",
    "wd_b":  "wd_b_testvector",
}

sim_tests: list[TestClass] = [
    TestClass( # basic SDP test
        # note that the common SDP model reads every cycle, but the testbench
        # still uses the rce signal to check read assertions
        params={"ADDRESS_WIDTH": 10, "DATA_WIDTH": 36},
        top="sync_ram_sdp",
        assertions=[],
        test_steps=[
            {"wce_a": 1, "wa_a": 0x0A, "wd_a": 0xdeadbeef},
            {"wce_a": 1, "wa_a": 0xBA, "wd_a": 0x5a5a5a5a},
            {"wce_a": 1, "wa_a": 0xFF, "wd_a": 0},
            {"rce_a": 1, "ra_a": 0x0A},
            {"rq_a": 0xdeadbeef},
            {"rce_a": 1, "ra_a": 0xFF},
            {"rq_a": 0},
        ]
    ),
    TestClass( # SDP read before write
        params={"ADDRESS_WIDTH": 4, "DATA_WIDTH": 16},
        top="sync_ram_sdp",
        assertions=[],
        test_steps=[
            {"wce_a": 1, "wa_a": 0xA, "wd_a": 0x1234},
            {"wce_a": 1, "wa_a": 0xA, "wd_a": 0x5678, "rce_a": 1, "ra_a": 0xA},
            {"rq_a": 0x1234, "rce_a": 1, "ra_a": 0xA},
            {"rq_a": 0x5678},
        ]
    ),
    TestClass( # basic TDP test 
        # note that the testbench uses ra and wa, while the common TDP model
        # uses a shared address
        params={"ADDRESS_WIDTH": 10, "DATA_WIDTH": 36},
        top="sync_ram_tdp",
        assertions=[],
        test_steps=[
            {"wce_a": 1, "ra_a": 0x0A,      "wce_b": 1, "ra_b": 0xBA, 
             "wd_a": 0xdeadbeef,            "wd_b": 0x5a5a5a5a},
            {"wce_a": 1, "ra_a": 0xFF, 
             "wd_a": 0},
            {"rce_a": 1, "ra_a": 0x0A,      "rce_b": 1, "ra_b": 0x0A},
            {"rq_a": 0xdeadbeef,            "rq_b": 0xdeadbeef},
            {"rce_a": 1, "ra_a": 0xFF,      "rce_b": 1, "ra_b": 0xBA},
            {"rq_a": 0,                     "rq_b": 0x5a5a5a5a},
        ]
    ),
    TestClass( # TDP with truncation
        params={"ADDRESS_WIDTH": 4, "DATA_WIDTH": 16},
        top="sync_ram_tdp",
        assertions=[],
        test_steps=[
            {"wce_a": 1, "ra_a": 0x0F,      "wce_b": 1, "ra_b": 0xBA, 
             "wd_a": 0xdeadbeef,            "wd_b": 0x5a5a5a5a},
            {"wce_a": 1, "ra_a": 0xFF, 
             "wd_a": 0},
            {"rce_a": 1, "ra_a": 0x0F,      "rce_b": 1, "ra_b": 0x0A},
            {"rq_a": 0,                     "rq_b": 0x00005a5a},
        ]
    ),
    TestClass( # TDP read before write
        # note that the testbench uses rce and wce, while the common TDP model
        # uses a single enable for write, with reads on no write
        params={"ADDRESS_WIDTH": 10, "DATA_WIDTH": 36},
        top="sync_ram_tdp",
        assertions=[],
        test_steps=[
            {"wce_a": 1, "ra_a": 0x0A,      "wce_b": 1, "ra_b": 0xBA, 
             "wd_a": 0xdeadbeef,            "wd_b": 0x5a5a5a5a},
            {"wce_a": 1, "ra_a": 0xBA,      "rce_b": 1, "ra_b": 0xBA,
             "wd_a": 0xa5a5a5a5},
            {                               "rq_b": 0x5a5a5a5a},
            {"rce_a": 1, "ra_a": 0x0A,      "rce_b": 1, "ra_b": 0x0A},
            {"rq_a": 0xdeadbeef,            "rq_b": 0xdeadbeef},
            {                               "rce_b": 1, "ra_b": 0xBA},
            {                               "rq_b": 0xa5a5a5a5},
        ]
    ),
    TestClass( # 2x wide write
        params={"ADDRESS_WIDTH": 11, "DATA_WIDTH": 18, "SHIFT_VAL": 1},
        top="sync_ram_sdp_wwr",
        assertions=[],
        test_steps=[
            {"wce_a": 1, "wa_a": 0b0000000001, "wd_a": 0xdeadbeef},
            {"rce_a": 0, "ra_a": 0b00000000010},
            {"rq_a": 0xdead},
            {"rce_a": 0, "ra_a": 0b00000000011},
            {"rq_a": 0xbeef},
        ]
    ),
    TestClass( # 4x wide write
        params={"ADDRESS_WIDTH": 10, "DATA_WIDTH": 8, "SHIFT_VAL": 2},
        top="sync_ram_sdp_wwr",
        assertions=[],
        test_steps=[
            {"wce_a": 1, "wa_a": 0b000100001, "wd_a": 0xdeadbeef},
            {"rce_a": 0, "ra_a": 0b00010000100},
            {"rq_a": 0xde},
            {"rce_a": 0, "ra_a": 0b00010000101},
            {"rq_a": 0xad},
            {"rce_a": 0, "ra_a": 0b00010000110},
            {"rq_a": 0xbe},
            {"rce_a": 0, "ra_a": 0b00010000111},
            {"rq_a": 0xef},
        ]
    ),
    TestClass( # 2x wide read
        params={"ADDRESS_WIDTH": 11, "DATA_WIDTH": 18, "SHIFT_VAL": 1},
        top="sync_ram_sdp_wrr",
        assertions=[],
        test_steps=[
            {"wce_a": 1, "wa_a": 0b00000000010, "wd_a": 0xdead},
            {"wce_a": 1, "wa_a": 0b00000000011, "wd_a": 0xbeef},
            {"rce_a": 0, "ra_a": 0b0000000001},
            {"rq_a": 0xdeadbeef},
        ]
    ),
    TestClass( # 4x wide read
        params={"ADDRESS_WIDTH": 10, "DATA_WIDTH": 8, "SHIFT_VAL": 2},
        top="sync_ram_sdp_wrr",
        assertions=[],
        test_steps=[
            {"wce_a": 1, "wa_a": 0b00010000100, "wd_a": 0xde},
            {"wce_a": 1, "wa_a": 0b00010000101, "wd_a": 0xad},
            {"wce_a": 1, "wa_a": 0b00010000110, "wd_a": 0xbe},
            {"wce_a": 1, "wa_a": 0b00010000111, "wd_a": 0xef},
            {"rce_a": 0, "ra_a": 0b000100001},
            {"rq_a": 0xdeadbeef},
        ]
    ),
    TestClass( # basic split SDP test
        params={"ADDRESS_WIDTH_A": 10, "DATA_WIDTH_A": 16,
                "ADDRESS_WIDTH_B": 10, "DATA_WIDTH_B": 16},
        top="double_sync_ram_sdp",
        assertions=[],
        test_steps=[
            {"wce_a": 1, "wa_a": 0x0A,      "wce_b": 1, "wa_b": 0xBA,
            "wd_a": 0x1234,                 "wd_b": 0x4567},
            {"wce_a": 1, "wa_a": 0xFF,      "wce_b": 1, "wa_b": 0x0A,
            "wd_a": 0,                      "wd_b": 0xbeef},
            {"rce_a": 1, "ra_a": 0x0A,      "rce_b": 1, "ra_b": 0x0A},
            {"rq_a": 0x1234,                "rq_b": 0xbeef},
        ]
    ),
]

for (params, top, assertions) in blockram_tests:
    sim_test = TestClass(
        params=dict(params),
        top=top,
        assertions=assertions,
        test_steps=None
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
            blockram_template.format(param_str=param_str, top=top),
            file=f
        )
        for assertion in sim_test.assertions:
            print("log ** CHECKING CELL COUNTS FOR TEST {top} WITH PARAMS{param_str}".format(param_str=param_str, top=top), file=f)
            print("select {}".format(assertion), file=f)
        print("", file=f)

        # prepare simulation tests
        test_steps = sim_test.test_steps
        if test_steps:
            if top == "sync_ram_sdp":
                uut_submodule = sync_ram_sdp_submodule
            elif top == "sync_ram_tdp":
                uut_submodule = sync_ram_tdp_submodule
            elif top == "sync_ram_sdp_wwr":
                uut_submodule = sync_ram_sdp_wwr_submodule
            elif top == "sync_ram_sdp_wrr":
                uut_submodule = sync_ram_sdp_wrr_submodule
            elif top == "double_sync_ram_sdp":
                uut_submodule = double_sync_ram_sdp_submodule
            else:
                raise NotImplementedError(f"missing submodule header for {top}")
            mem_test_vector = ""
            for step, test in enumerate(test_steps):
                for key, val in test.items():
                    key = test_val_map[key]
                    mem_test_vector += f"\\\n{key}[{step}] = 'h{val:x};"
            print(
                sim_template.format(
                    top=top,
                    mem_test_vector=mem_test_vector,
                    uut_submodule=uut_submodule,
                    param_str=param_str,
                    vectorlen=len(test_steps) + 2
                ), file=f
            )
            # simulation counts for 2 tests
            j += 1

        # increment test counter
        j += 1
        if j >= max_j:
            f = f.close()
            i += 1

if f:
    f.close()
