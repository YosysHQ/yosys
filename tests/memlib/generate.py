# TODO:

# - priority logic
# - swizzles for weird width progressions


class Test:
    def __init__(self, name, src, libs, defs, cells):
        self.name = name
        self.src = src
        self.libs = libs
        self.defs = defs
        self.cells = cells

TESTS = []

### basic sanity tests
# Asynchronous-read RAM

ASYNC = """
module top(clk, ra, wa, rd, wd, we);

localparam ABITS = {abits};
localparam DBITS = {dbits};

input wire clk;
input wire we;
input wire [ABITS-1:0] ra, wa;
input wire [DBITS-1:0] wd;
output wire [DBITS-1:0] rd;

reg [DBITS-1:0] mem [0:2**ABITS-1];

always @(posedge clk)
    if (we)
        mem[wa] <= wd;

assign rd = mem[ra];

endmodule
"""

ASYNC_SMALL = ASYNC.format(abits=6, dbits=6)
ASYNC_BIG = ASYNC.format(abits=11, dbits=10)

TESTS += [
    Test("async_big", ASYNC_BIG, ["lut", "block_tdp"], [], {"RAM_LUT": 384}),
    Test("async_big_block", ASYNC_BIG, ["block_tdp"], [], {"RAM_BLOCK_TDP": 0}),
    Test("async_small", ASYNC_SMALL, ["lut", "block_tdp"], [], {"RAM_LUT": 8}),
    Test("async_small_block", ASYNC_SMALL, ["block_tdp"], [], {"RAM_BLOCK_TDP": 0}),
]

# Synchronous SDP read first
SYNC = """
module top(clk, ra, wa, rd, wd, we);

localparam ABITS = {abits};
localparam DBITS = {dbits};

input wire clk;
input wire we;
input wire [ABITS-1:0] ra, wa;
input wire [DBITS-1:0] wd;
output reg [DBITS-1:0] rd;

{attr}
reg [DBITS-1:0] mem [0:2**ABITS-1];

always @(posedge clk)
    if (we)
        mem[wa] <= wd;

always @(posedge clk)
    rd <= mem[ra];

endmodule
"""

SYNC_SMALL = SYNC.format(abits=6, dbits=6, attr="")
SYNC_SMALL_BLOCK = SYNC.format(abits=6, dbits=6, attr='(* ram_style="block" *)')
SYNC_BIG = SYNC.format(abits=11, dbits=10, attr="")
SYNC_MID = SYNC.format(abits=6, dbits=16, attr="")

TESTS += [
    Test("sync_big", SYNC_BIG, ["lut", "block_tdp"], [], {"RAM_BLOCK_TDP": 20}),
    Test("sync_big_sdp", SYNC_BIG, ["lut", "block_sdp"], [], {"RAM_BLOCK_SDP": 20}),
    Test("sync_big_lut", SYNC_BIG, ["lut"], [], {"RAM_LUT": 384}),
    Test("sync_small", SYNC_SMALL, ["lut", "block_tdp"], [], {"RAM_LUT": 8}),
    Test("sync_small_block", SYNC_SMALL, ["block_tdp"], [], {"RAM_BLOCK_TDP": 1}),
    Test("sync_small_block_attr", SYNC_SMALL_BLOCK, ["lut", "block_tdp"], [], {"RAM_BLOCK_TDP": 1}),
]

### initialization values testing
LUT_INIT = """
module top(clk, ra, wa, rd, wd, we);

localparam ABITS = {abits};
localparam DBITS = {dbits};

input wire clk;
input wire we;
input wire [ABITS-1:0] ra, wa;
input wire [DBITS-1:0] wd;
output wire [DBITS-1:0] rd;

reg [DBITS-1:0] mem [0:2**ABITS-1];

integer i;
initial
	for (i = 0; i < 2**ABITS-1; i = i + 1)
		mem[i] = {ival};

always @(posedge clk)
    if (we)
        mem[wa] <= wd;

assign rd = mem[ra];

endmodule
"""

INIT_LUT_ZEROS = LUT_INIT.format(abits=4, dbits=4, ival=0);
INIT_LUT_VAL = LUT_INIT.format(abits=4, dbits=4, ival=5);
INIT_LUT_VAL2 = LUT_INIT.format(abits=6, dbits=6, ival="6'h12");
INIT_LUT_X = LUT_INIT.format(abits=4, dbits=4, ival="4'hx")

TESTS += [
	Test("init_lut_zeros_zero", INIT_LUT_ZEROS, ["lut"], ["INIT_ZERO"], {"RAM_LUT":1}),
	Test("init_lut_zeros_any", INIT_LUT_ZEROS, ["lut"], ["INIT_ANY"], {"RAM_LUT":1}),
	Test("init_lut_val_zero", INIT_LUT_VAL, ["lut"], ["INIT_ZERO"], {"RAM_LUT":0}), #CHECK: no emulation?
	Test("init_lut_val_any", INIT_LUT_VAL, ["lut"], ["INIT_ANY"], {"RAM_LUT":1}),
	Test("init_lut_val_no_undef", INIT_LUT_VAL, ["lut"], ["INIT_NO_UNDEF"], {"RAM_LUT":1}),
	Test("init_lut_val2_any", INIT_LUT_VAL2, ["lut"], ["INIT_ANY"], {"RAM_LUT":8}),
	Test("init_lut_val2_no_undef", INIT_LUT_VAL2, ["lut"], ["INIT_NO_UNDEF"], {"RAM_LUT":8}),
	Test("init_lut_x_none", INIT_LUT_X, ["lut"], ["INIT_NONE"], {"RAM_LUT":1}),
	Test("init_lut_x_zero", INIT_LUT_X, ["lut"], ["INIT_ZERO"], {"RAM_LUT":1}),
	Test("init_lut_x_any", INIT_LUT_X, ["lut"], ["INIT_ANY"], {"RAM_LUT":1}),
	Test("init_lut_x_no_undef", INIT_LUT_X, ["lut"], ["INIT_NO_UNDEF"], {"RAM_LUT":1}),
]

### width testing 9-bit-per-byte
RAM_9b1B = """
module top(clk, ra, wa, rd, wd, we);

localparam ABITS = {abits};
localparam DBITS = {dbits};

input wire clk;
input wire we;
input wire [ABITS-1:0] ra, wa;
input wire [DBITS-1:0] wd;
output reg [DBITS-1:0] rd;

reg [DBITS-1:0] mem [0:2**ABITS-1];

always @(posedge clk)
    if (we)
        mem[wa] <= wd;

always @(posedge clk)
    rd <= mem[ra];

endmodule
"""

RAM_18b2B = RAM_9b1B.format(abits=3, dbits=18);
RAM_9b1B = RAM_9b1B.format(abits=4, dbits=9);
RAM_4b1B = RAM_9b1B.format(abits=5, dbits=4);
RAM_2b1B = RAM_9b1B.format(abits=6, dbits=2);
RAM_1b1B = RAM_9b1B.format(abits=7, dbits=1);

TESTS += [
	Test("ram_18b2B", RAM_18b2B, ["9b1B"], [], {"RAM_9b1B":1}),
	Test("ram_9b1B", RAM_9b1B, ["9b1B"], [], {"RAM_9b1B":1}),
	Test("ram_4b1B", RAM_4b1B, ["9b1B"], [], {"RAM_9b1B":1}),
	Test("ram_2b1B", RAM_2b1B, ["9b1B"], [], {"RAM_9b1B":1}),
	Test("ram_1b1B", RAM_1b1B, ["9b1B"], [], {"RAM_9b1B":1}),
]

### initializing 9-bits-per-byte
RAM_9b1B_init = """
module top(clk, ra, wa, rd, wd, we);

localparam ABITS = {abits};
localparam DBITS = {dbits};

input wire clk;
input wire we;
input wire [ABITS-1:0] ra, wa;
input wire [DBITS-1:0] wd;
output reg [DBITS-1:0] rd;

reg [DBITS-1:0] mem [0:2**ABITS-1];

integer i;
initial
	for (i = 0; i < 2**ABITS-1; i = i + 1)
		mem[i] = {ival};

always @(posedge clk)
    if (we)
        mem[wa] <= wd;

always @(posedge clk)
    rd <= mem[ra];

endmodule
"""

INIT_9b1B_ZEROS = RAM_9b1B_init.format(abits=4, dbits=9, ival=0);
INIT_9b1B_VAL = RAM_9b1B_init.format(abits=4, dbits=9, ival=275);
INIT_13b2B_VAL = RAM_9b1B_init.format(abits=3, dbits=13, ival="13'h01f3")
INIT_18b2B_VAL = RAM_9b1B_init.format(abits=4, dbits=18, ival="18'h1f39a");
INIT_4b1B_X = RAM_9b1B_init.format(abits=5, dbits=4, ival="4'hx")

TESTS += [
	Test("init_9b1B_zeros_zero", INIT_9b1B_ZEROS, ["9b1B"], ["INIT_ZERO"], {"RAM_9b1B":1}),
	Test("init_9b1B_zeros_any", INIT_9b1B_ZEROS, ["9b1B"], ["INIT_ANY"], {"RAM_9b1B":1}),
	Test("init_9b1B_val_zero", INIT_9b1B_VAL, ["9b1B"], ["INIT_ZERO"], {"RAM_9b1B":0}), #CHECK: no emulation?
	Test("init_9b1B_val_any", INIT_9b1B_VAL, ["9b1B"], ["INIT_ANY"], {"RAM_9b1B":1}),
	Test("init_9b1B_val_no_undef", INIT_9b1B_VAL, ["9b1B"], ["INIT_NO_UNDEF"], {"RAM_9b1B":1}),
	Test("init_13b2B_val_any", INIT_13b2B_VAL, ["9b1B"], ["INIT_ANY"], {"RAM_9b1B":1}),
	Test("init_18b2B_val_any", INIT_18b2B_VAL, ["9b1B"], ["INIT_ANY"], {"RAM_9b1B":2}),
	Test("init_18b2B_val_no_undef", INIT_18b2B_VAL, ["9b1B"], ["INIT_NO_UNDEF"], {"RAM_9b1B":2}),
	Test("init_4b1B_x_none", INIT_4b1B_X, ["9b1B"], ["INIT_NONE"], {"RAM_9b1B":1}),
	Test("init_4b1B_x_zero", INIT_4b1B_X, ["9b1B"], ["INIT_ZERO"], {"RAM_9b1B":1}),
	Test("init_4b1B_x_any", INIT_4b1B_X, ["9b1B"], ["INIT_ANY"], {"RAM_9b1B":1}),
	Test("init_4b1B_x_no_undef", INIT_4b1B_X, ["9b1B"], ["INIT_NO_UNDEF"], {"RAM_9b1B":1}),
]

### Clock polarity combinations
# I'm not entirely convinced auto-test is correctly testing clock edging
#  but they do at least all gen/synth
SYNCCLOCK = """
module top(clk, ra, wa, rd, wd, we);

localparam ABITS = {abits};
localparam DBITS = 8;

input wire clk;
input wire we;
input wire [ABITS-1:0] ra, wa;
input wire [DBITS-1:0] wd;
output reg [DBITS-1:0] rd;

reg [DBITS-1:0] mem [0:2**ABITS-1];

always @(posedge clk)
    if (we)
        mem[wa] <= wd;

always @(posedge clk)
    rd <= mem[ra];

endmodule
"""
for (abits, cnt, wclk, rclk, shared) in [
	(4,   1, "ANY","ANY", False),
	(4,   1, "ANY","NEG", False),
	(4,   1, "ANY","POS", False),
	(4,   1, "NEG","ANY", False),
	(4,   1, "NEG","POS", False),
	(4,   1, "NEG","NEG", False),
	(4,   1, "POS","ANY", False),
	(4,   1, "POS","NEG", False),
	(4,   1, "POS","POS", False),
	(4,   1, "ANY","ANY", True),
	(4,   0, "NEG","POS", True), # FF mapping
	(4,   1, "NEG","NEG", True),
	(4,   0, "POS","NEG", True), # FF mapping
	(4,   1, "POS","POS", True),
	# cannot combine "ANY" with "POS|NEG" when using shared clock
]:
	name = f"clock_a{abits}_w{wclk}r{rclk}s{shared}"
	defs = ["WCLK_" + wclk, "RCLK_" + rclk]
	if (shared):
		defs.append("SHARED_CLK")
	TESTS.append(Test(
		name, SYNCCLOCK.format(abits=abits),
		["clock_sdp"], defs, {"RAM_CLOCK_SDP": cnt}
	))

### mixed width testing
# Wide write port
MIXED_WRITE = """
module top(clk, ra, wa, rd, wd, we);

localparam WABITS = {wabits};
localparam WDBITS = {wdbits};

localparam RABITS = {rabits};
localparam RDBITS = {rdbits};

input wire clk;
input wire we;
input wire [WABITS-1:0] wa;
input wire [WDBITS-1:0] wd;
input wire [RABITS-1:0] ra;
output reg [RDBITS-1:0] rd;

localparam DEPTH = (2**WABITS);

localparam OFFSET = RABITS-WABITS;

(* syn_ramstyle = "block_ram" *)
reg [WDBITS-1:0] mem [0:DEPTH-1];

always @(posedge clk)
	if (we)
		mem[wa] <= wd;

if (OFFSET > 0) begin
	reg [WDBITS-1:0] mem_read;
	reg [OFFSET-1:0] subaddr_r;
	always @(posedge clk) begin
		mem_read <= mem[ra[RABITS-1:OFFSET]];
		subaddr_r <= ra[OFFSET-1:0];
	end

	always @(mem_read, subaddr_r)
		rd <= mem_read[subaddr_r*RDBITS+:RDBITS];
end 
else 
begin
	always @(posedge clk)
		case (OFFSET)
		0:  rd <= mem[ra];
		-1: rd <= {{ mem[ra], mem[ra+1] }};
		endcase
end
endmodule
"""

UNMIXED = MIXED_WRITE.format(wabits=4, wdbits=9, rabits=4, rdbits=9)
MIXED_9_18 = MIXED_WRITE.format(wabits=5, wdbits=9, rabits=4, rdbits=18)
MIXED_18_9 = MIXED_WRITE.format(wabits=3, wdbits=18, rabits=4, rdbits=9)
MIXED_36_9 = MIXED_WRITE.format(wabits=3, wdbits=36, rabits=5, rdbits=9)
MIXED_4_2 = MIXED_WRITE.format(wabits=5, wdbits=4, rabits=6, rdbits=2);

TESTS += [
	Test("unmixed", UNMIXED, ["9b1B"], [], {"RAM_9b1B":1}),
	Test("mixed_9_18", MIXED_9_18, ["9b1B"], [], {"RAM_9b1B":4}), #CHECK: only using half the memory
	Test("mixed_18_9", MIXED_18_9, ["9b1B"], [], {"RAM_9b1B":1}),
	Test("mixed_36_9", MIXED_36_9, ["9b1B"], [], {"RAM_9b1B":2}),
	Test("mixed_4_2", MIXED_4_2, ["9b1B"], [], {"RAM_9b1B":1}),
]

### basic TDP test

TDP = """
module top(clka, clkb, addra, addrb, rda, rdb, wda, wdb, wea, web);

localparam ABITS = 6;
localparam DBITS = 6;

input wire clka, clkb;
input wire wea, web;
input wire [ABITS-1:0] addra, addrb;
input wire [DBITS-1:0] wda, wdb;
output reg [DBITS-1:0] rda, rdb;

reg [DBITS-1:0] mem [0:2**ABITS-1];

always @(posedge clka)
    if (wea)
        mem[addra] <= wda;
    else
        rda <= mem[addra];

always @(posedge clkb)
    if (web)
        mem[addrb] <= wdb;
    else
        rdb <= mem[addrb];

endmodule
"""

TESTS += [
    Test("tdp", TDP, ["block_tdp", "block_sdp"], [], {"RAM_BLOCK_TDP": 1}),
]

# shared clock
# Synchronous SDP with clock domain crossing
SYNC_2CLK = """
module top(rclk, wclk, ra, wa, rd, wd, we);

localparam ABITS = 6;
localparam DBITS = 16;

input wire rclk, wclk;
input wire we;
input wire [ABITS-1:0] ra, wa;
input wire [DBITS-1:0] wd;
output reg [DBITS-1:0] rd;

reg [DBITS-1:0] mem [0:2**ABITS-1];

always @(posedge wclk)
    if (we)
        mem[wa] <= wd;

always @(posedge rclk)
    rd <= mem[ra];

endmodule
"""

TESTS += [
        Test("sync_2clk", SYNC_2CLK, ["block_sdp"], [], {"RAM_BLOCK_SDP": 1}),
        Test("sync_shared", SYNC_MID, ["block_sdp_1clk"], [], {"RAM_BLOCK_SDP_1CLK": 1}),
        Test("sync_2clk_shared", SYNC_2CLK, ["block_sdp_1clk"], [], {"RAM_BLOCK_SDP_1CLK": 0}),
]

# inter-port transparency
# Synchronous SDP with write-first behaviour
SYNC_TRANS = """
module top(clk, ra, wa, rd, wd, we);

localparam ABITS = 6;
localparam DBITS = 16;

input wire clk;
input wire we;
input wire [ABITS-1:0] ra, wa;
input wire [DBITS-1:0] wd;
output reg [DBITS-1:0] rd;

reg [DBITS-1:0] mem [0:2**ABITS-1];

always @(negedge clk)
    if (we)
        mem[wa] <= wd;

always @(negedge clk) begin
    rd <= mem[ra];
    if (we && ra == wa)
        rd <= wd;
end

endmodule
"""

TESTS += [
        Test("sync_trans_old_old", SYNC_MID, ["block_sdp_1clk"], ["TRANS_OLD"], {"RAM_BLOCK_SDP_1CLK": (1, {"OPTION_TRANS": 0})}),
        Test("sync_trans_old_new", SYNC_MID, ["block_sdp_1clk"], ["TRANS_NEW"], {"RAM_BLOCK_SDP_1CLK": 1}),
        Test("sync_trans_old_none", SYNC_MID, ["block_sdp_1clk"], [], {"RAM_BLOCK_SDP_1CLK": 1}),
        Test("sync_trans_new_old", SYNC_TRANS, ["block_sdp_1clk"], ["TRANS_OLD"], {"RAM_BLOCK_SDP_1CLK": 1}),
        Test("sync_trans_new_new", SYNC_TRANS, ["block_sdp_1clk"], ["TRANS_NEW"], {"RAM_BLOCK_SDP_1CLK": (1, {"OPTION_TRANS": 1})}),
        Test("sync_trans_new_none", SYNC_TRANS, ["block_sdp_1clk"], [], {"RAM_BLOCK_SDP_1CLK": 1}),
]

# rdwr checks
# Synchronous single-port RAM with mutually exclusive read/write
SP_NO_CHANGE = """
module top(clk, addr, rd, wd, we);

input wire clk;
input wire we;
input wire [3:0] addr;
input wire [15:0] wd;
output reg [15:0] rd;

reg [15:0] mem [0:15];

always @(negedge clk) begin
    if (we)
        mem[addr] <= wd;
    else
        rd <= mem[addr];
end

endmodule
"""

SP_NO_CHANGE_BE = """
module top(clk, addr, rd, wd, we);

input wire clk;
input wire [1:0] we;
input wire [3:0] addr;
input wire [15:0] wd;
output reg [15:0] rd;

reg [15:0] mem [0:15];

always @(negedge clk) begin
    if (we) begin
        if (we[0])
            mem[addr][7:0] <= wd[7:0];
        if (we[1])
            mem[addr][15:8] <= wd[15:8];
    end else
        rd <= mem[addr];
end

endmodule
"""

# Synchronous single-port RAM with write-first behaviour
SP_NEW = """
module top(clk, addr, rd, wd, we);

input wire clk;
input wire we;
input wire [3:0] addr;
input wire [15:0] wd;
output reg [15:0] rd;

reg [15:0] mem [0:15];

always @(negedge clk) begin
    if (we) begin
        mem[addr] <= wd;
        rd <= wd;
    end else
        rd <= mem[addr];
end

endmodule
"""

SP_NEW_BE = """
module top(clk, addr, rd, wd, we);

input wire clk;
input wire [1:0] we;
input wire [3:0] addr;
input wire [15:0] wd;
output reg [15:0] rd;

reg [15:0] mem [0:15];

always @(negedge clk) begin
    rd <= mem[addr];
    if (we[0]) begin
        mem[addr][7:0] <= wd[7:0];
        rd[7:0] <= wd[7:0];
    end
    if (we[1]) begin
        mem[addr][15:8] <= wd[15:8];
        rd[15:8] <= wd[15:8];
    end
end

endmodule
"""

# Synchronous single-port RAM with read-first behaviour
SP_OLD = """
module top(clk, addr, rd, wd, we);

input wire clk;
input wire we;
input wire [3:0] addr;
input wire [15:0] wd;
output reg [15:0] rd;

reg [15:0] mem [0:15];

always @(negedge clk) begin
    if (we)
        mem[addr] <= wd;
    rd <= mem[addr];
end

endmodule
"""

SP_OLD_BE = """
module top(clk, addr, rd, wd, we);

input wire clk;
input wire [1:0] we;
input wire [3:0] addr;
input wire [15:0] wd;
output reg [15:0] rd;

reg [15:0] mem [0:15];

always @(negedge clk) begin
    if (we[0])
        mem[addr][7:0] <= wd[7:0];
    if (we[1])
        mem[addr][15:8] <= wd[15:8];
    rd <= mem[addr];
end

endmodule
"""

TESTS += [
        Test("sp_nc_none", SP_NO_CHANGE, ["block_sp"], [], {"RAM_BLOCK_SP": 1}),
        Test("sp_new_none", SP_NEW, ["block_sp"], [], {"RAM_BLOCK_SP": 1}),
        Test("sp_old_none", SP_OLD, ["block_sp"], [], {"RAM_BLOCK_SP": 0}),
        Test("sp_nc_nc", SP_NO_CHANGE, ["block_sp"], ["RDWR_NO_CHANGE"], {"RAM_BLOCK_SP": 1}),
        Test("sp_new_nc", SP_NEW, ["block_sp"], ["RDWR_NO_CHANGE"], {"RAM_BLOCK_SP": 1}),
        Test("sp_old_nc", SP_OLD, ["block_sp"], ["RDWR_NO_CHANGE"], {"RAM_BLOCK_SP": 0}),
        Test("sp_nc_new", SP_NO_CHANGE, ["block_sp"], ["RDWR_NEW"], {"RAM_BLOCK_SP": 1}),
        Test("sp_new_new", SP_NEW, ["block_sp"], ["RDWR_NEW"], {"RAM_BLOCK_SP": 1}),
        Test("sp_old_new", SP_OLD, ["block_sp"], ["RDWR_NEW"], {"RAM_BLOCK_SP": 0}),
        Test("sp_nc_old", SP_NO_CHANGE, ["block_sp"], ["RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
        Test("sp_new_old", SP_NEW, ["block_sp"], ["RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
        Test("sp_old_old", SP_OLD, ["block_sp"], ["RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
        Test("sp_nc_new_only", SP_NO_CHANGE, ["block_sp"], ["RDWR_NEW_ONLY"], {"RAM_BLOCK_SP": 1}),
        Test("sp_new_new_only", SP_NEW, ["block_sp"], ["RDWR_NEW_ONLY"], {"RAM_BLOCK_SP": 1}),
        Test("sp_old_new_only", SP_OLD, ["block_sp"], ["RDWR_NEW_ONLY"], {"RAM_BLOCK_SP": 0}),
        Test("sp_nc_new_only_be", SP_NO_CHANGE_BE, ["block_sp"], ["RDWR_NEW_ONLY"], {"RAM_BLOCK_SP": 1}),
        Test("sp_new_new_only_be", SP_NEW_BE, ["block_sp"], ["RDWR_NEW_ONLY"], {"RAM_BLOCK_SP": 2}),
        Test("sp_old_new_only_be", SP_OLD_BE, ["block_sp"], ["RDWR_NEW_ONLY"], {"RAM_BLOCK_SP": 0}),
        Test("sp_nc_new_be", SP_NO_CHANGE_BE, ["block_sp"], ["RDWR_NEW"], {"RAM_BLOCK_SP": 1}),
        Test("sp_new_new_be", SP_NEW_BE, ["block_sp"], ["RDWR_NEW"], {"RAM_BLOCK_SP": 1}),
        Test("sp_old_new_be", SP_OLD_BE, ["block_sp"], ["RDWR_NEW"], {"RAM_BLOCK_SP": 0}),
        Test("sp_nc_old_be", SP_NO_CHANGE_BE, ["block_sp"], ["RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
        Test("sp_new_old_be", SP_NEW_BE, ["block_sp"], ["RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
        Test("sp_old_old_be", SP_OLD_BE, ["block_sp"], ["RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
        Test("sp_nc_nc_be", SP_NO_CHANGE_BE, ["block_sp"], ["RDWR_NO_CHANGE"], {"RAM_BLOCK_SP": 1}),
        Test("sp_new_nc_be", SP_NEW_BE, ["block_sp"], ["RDWR_NO_CHANGE"], {"RAM_BLOCK_SP": 2}),
        Test("sp_old_nc_be", SP_OLD_BE, ["block_sp"], ["RDWR_NO_CHANGE"], {"RAM_BLOCK_SP": 0}),
        Test("sp_nc_auto", SP_NO_CHANGE, ["block_sp"], ["RDWR_NO_CHANGE", "RDWR_OLD", "RDWR_NEW"], {"RAM_BLOCK_SP": 1}),
        Test("sp_new_auto", SP_NEW, ["block_sp"], ["RDWR_NO_CHANGE", "RDWR_OLD", "RDWR_NEW"], {"RAM_BLOCK_SP": (1, {"OPTION_RDWR": "NEW"})}),
        Test("sp_old_auto", SP_OLD, ["block_sp"], ["RDWR_NO_CHANGE", "RDWR_OLD", "RDWR_NEW"], {"RAM_BLOCK_SP": (1, {"OPTION_RDWR": "OLD"})}),
        Test("sp_nc_auto_be", SP_NO_CHANGE_BE, ["block_sp"], ["RDWR_NO_CHANGE", "RDWR_OLD", "RDWR_NEW"], {"RAM_BLOCK_SP": 1}),
        Test("sp_new_auto_be", SP_NEW_BE, ["block_sp"], ["RDWR_NO_CHANGE", "RDWR_OLD", "RDWR_NEW"], {"RAM_BLOCK_SP": (1, {"OPTION_RDWR": "NEW"})}),
        Test("sp_old_auto_be", SP_OLD_BE, ["block_sp"], ["RDWR_NO_CHANGE", "RDWR_OLD", "RDWR_NEW"], {"RAM_BLOCK_SP": (1, {"OPTION_RDWR": "OLD"})}),
]

# Synchronous read port with initial value
SP_INIT = """
module top(clk, addr, rd, wd, we, re);

input wire clk;
input wire we, re;
input wire [3:0] addr;
input wire [15:0] wd;
output reg [15:0] rd;

reg [15:0] mem [0:15];

initial rd = {ival};

always @(posedge clk) begin
    if (we)
        mem[addr] <= wd;
    if (re)
        rd <= mem[addr];
end

endmodule
"""

SP_INIT_X = SP_INIT.format(ival="16'hxxxx")
SP_INIT_0 = SP_INIT.format(ival="16'h0000")
SP_INIT_V = SP_INIT.format(ival="16'h55aa")

TESTS += [
    Test("sp_init_x_x", SP_INIT_X, ["block_sp"], ["RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_init_x_x_re", SP_INIT_X, ["block_sp"], ["RDEN", "RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_init_x_x_ce", SP_INIT_X, ["block_sp"], ["CLKEN", "RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_init_0_x", SP_INIT_0, ["block_sp"], ["RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_init_0_x_re", SP_INIT_0, ["block_sp"], ["RDEN", "RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_init_0_0", SP_INIT_0, ["block_sp"], ["RDINIT_0", "RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_init_0_0_re", SP_INIT_0, ["block_sp"], ["RDINIT_0", "RDEN", "RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_init_0_any", SP_INIT_0, ["block_sp"], ["RDINIT_ANY", "RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_init_0_any_re", SP_INIT_0, ["block_sp"], ["RDINIT_ANY", "RDEN", "RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_init_v_x", SP_INIT_V, ["block_sp"], ["RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_init_v_x_re", SP_INIT_V, ["block_sp"], ["RDEN", "RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_init_v_0", SP_INIT_V, ["block_sp"], ["RDINIT_0", "RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_init_v_0_re", SP_INIT_V, ["block_sp"], ["RDINIT_0", "RDEN", "RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_init_v_any", SP_INIT_V, ["block_sp"], ["RDINIT_ANY", "RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_init_v_any_re", SP_INIT_V, ["block_sp"], ["RDINIT_ANY", "RDEN", "RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
]

# Synchronous read port with asynchronous reset
SP_ARST = """
module top(clk, addr, rd, wd, we, re, ar);

input wire clk;
input wire we, re, ar;
input wire [3:0] addr;
input wire [15:0] wd;
output reg [15:0] rd;

reg [15:0] mem [0:15];

initial rd = {ival};

always @(posedge clk) begin
    if (we)
        mem[addr] <= wd;
end
always @(posedge clk, posedge ar) begin
    if (ar)
        rd <= {aval};
    else if (re)
        rd <= mem[addr];
end

endmodule
"""

SP_ARST_X = SP_ARST.format(ival="16'hxxxx", aval="16'hxxxx")
SP_ARST_0 = SP_ARST.format(ival="16'hxxxx", aval="16'h0000")
SP_ARST_V = SP_ARST.format(ival="16'hxxxx", aval="16'h55aa")
SP_ARST_E = SP_ARST.format(ival="16'h55aa", aval="16'h55aa")
SP_ARST_N = SP_ARST.format(ival="16'h1234", aval="16'h55aa")

TESTS += [
    Test("sp_arst_x_x", SP_ARST_X, ["block_sp"], ["RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_arst_x_x_re", SP_ARST_X, ["block_sp"], ["RDEN", "RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_arst_0_x", SP_ARST_0, ["block_sp"], ["RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_arst_0_x_re", SP_ARST_0, ["block_sp"], ["RDEN", "RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_arst_0_0", SP_ARST_0, ["block_sp"], ["RDINIT_ANY", "RDARST_0", "RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_arst_0_0_re", SP_ARST_0, ["block_sp"], ["RDINIT_ANY", "RDARST_0", "RDEN", "RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_arst_0_any", SP_ARST_0, ["block_sp"], ["RDINIT_ANY", "RDARST_ANY", "RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_arst_0_any_re", SP_ARST_0, ["block_sp"], ["RDINIT_ANY", "RDARST_ANY", "RDEN", "RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_arst_0_init", SP_ARST_0, ["block_sp"], ["RDINIT_ANY", "RDARST_INIT", "RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_arst_0_init_re", SP_ARST_0, ["block_sp"], ["RDINIT_ANY", "RDARST_INIT", "RDEN", "RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_arst_v_x", SP_ARST_V, ["block_sp"], ["RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_arst_v_x_re", SP_ARST_V, ["block_sp"], ["RDEN", "RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_arst_v_0", SP_ARST_V, ["block_sp"], ["RDINIT_ANY", "RDARST_0", "RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_arst_v_0_re", SP_ARST_V, ["block_sp"], ["RDINIT_ANY", "RDARST_0", "RDEN", "RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_arst_v_any", SP_ARST_V, ["block_sp"], ["RDINIT_ANY", "RDARST_ANY", "RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_arst_v_any_re", SP_ARST_V, ["block_sp"], ["RDINIT_ANY", "RDARST_ANY", "RDEN", "RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_arst_v_init", SP_ARST_V, ["block_sp"], ["RDINIT_ANY", "RDARST_INIT", "RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_arst_v_init_re", SP_ARST_V, ["block_sp"], ["RDINIT_ANY", "RDARST_INIT", "RDEN", "RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_arst_e_x", SP_ARST_E, ["block_sp"], ["RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_arst_e_x_re", SP_ARST_E, ["block_sp"], ["RDEN", "RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_arst_e_0", SP_ARST_E, ["block_sp"], ["RDINIT_ANY", "RDARST_0", "RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_arst_e_0_re", SP_ARST_E, ["block_sp"], ["RDINIT_ANY", "RDARST_0", "RDEN", "RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_arst_e_any", SP_ARST_E, ["block_sp"], ["RDINIT_ANY", "RDARST_ANY", "RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_arst_e_any_re", SP_ARST_E, ["block_sp"], ["RDINIT_ANY", "RDARST_ANY", "RDEN", "RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_arst_e_init", SP_ARST_E, ["block_sp"], ["RDINIT_ANY", "RDARST_INIT", "RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_arst_e_init_re", SP_ARST_E, ["block_sp"], ["RDINIT_ANY", "RDARST_INIT", "RDEN", "RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_arst_n_x", SP_ARST_N, ["block_sp"], ["RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_arst_n_x_re", SP_ARST_N, ["block_sp"], ["RDEN", "RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_arst_n_0", SP_ARST_N, ["block_sp"], ["RDINIT_ANY", "RDARST_0", "RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_arst_n_0_re", SP_ARST_N, ["block_sp"], ["RDINIT_ANY", "RDARST_0", "RDEN", "RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_arst_n_any", SP_ARST_N, ["block_sp"], ["RDINIT_ANY", "RDARST_ANY", "RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_arst_n_any_re", SP_ARST_N, ["block_sp"], ["RDINIT_ANY", "RDARST_ANY", "RDEN", "RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_arst_n_init", SP_ARST_N, ["block_sp"], ["RDINIT_ANY", "RDARST_INIT", "RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_arst_n_init_re", SP_ARST_N, ["block_sp"], ["RDINIT_ANY", "RDARST_INIT", "RDEN", "RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
]

# Synchronous read port with synchronous reset (reset priority over enable)
SP_SRST = """
module top(clk, addr, rd, wd, we, re, sr);

input wire clk;
input wire we, re, sr;
input wire [3:0] addr;
input wire [15:0] wd;
output reg [15:0] rd;

reg [15:0] mem [0:15];

initial rd = {ival};

always @(posedge clk) begin
    if (we)
        mem[addr] <= wd;
end
always @(posedge clk) begin
    if (sr)
        rd <= {sval};
    else if (re)
        rd <= mem[addr];
end

endmodule
"""

# Synchronous read port with synchronous reet (enable priority over reset)
SP_SRST_G = """
module top(clk, addr, rd, wd, we, re, sr);

input wire clk;
input wire we, re, sr;
input wire [3:0] addr;
input wire [15:0] wd;
output reg [15:0] rd;

reg [15:0] mem [0:15];

initial rd = {ival};

always @(posedge clk) begin
    if (we)
        mem[addr] <= wd;
end
always @(posedge clk) begin
    if (re) begin
        if (sr)
            rd <= {sval};
        else
            rd <= mem[addr];
    end
end

endmodule
"""

SP_SRST_X = SP_SRST.format(ival="16'hxxxx", sval="16'hxxxx")
SP_SRST_0 = SP_SRST.format(ival="16'hxxxx", sval="16'h0000")
SP_SRST_V = SP_SRST.format(ival="16'hxxxx", sval="16'h55aa")
SP_SRST_E = SP_SRST.format(ival="16'h55aa", sval="16'h55aa")
SP_SRST_N = SP_SRST.format(ival="16'h1234", sval="16'h55aa")
SP_SRST_GV = SP_SRST_G.format(ival="16'hxxxx", sval="16'h55aa")

TESTS += [
    Test("sp_srst_x_x", SP_SRST_X, ["block_sp"], ["RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_srst_x_x_re", SP_SRST_X, ["block_sp"], ["RDEN", "RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_srst_0_x", SP_SRST_0, ["block_sp"], ["RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_srst_0_x_re", SP_SRST_0, ["block_sp"], ["RDEN", "RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_srst_0_0", SP_SRST_0, ["block_sp"], ["RDINIT_ANY", "RDSRST_0", "RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_srst_0_0_re", SP_SRST_0, ["block_sp"], ["RDINIT_ANY", "RDSRST_0", "RDEN", "RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_srst_0_any", SP_SRST_0, ["block_sp"], ["RDINIT_ANY", "RDSRST_ANY", "RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_srst_0_any_re", SP_SRST_0, ["block_sp"], ["RDINIT_ANY", "RDSRST_ANY", "RDEN", "RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_srst_0_init", SP_SRST_0, ["block_sp"], ["RDINIT_ANY", "RDSRST_INIT", "RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_srst_0_init_re", SP_SRST_0, ["block_sp"], ["RDINIT_ANY", "RDSRST_INIT", "RDEN", "RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_srst_v_x", SP_SRST_V, ["block_sp"], ["RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_srst_v_x_re", SP_SRST_V, ["block_sp"], ["RDEN", "RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_srst_v_0", SP_SRST_V, ["block_sp"], ["RDINIT_ANY", "RDSRST_0", "RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_srst_v_0_re", SP_SRST_V, ["block_sp"], ["RDINIT_ANY", "RDSRST_0", "RDEN", "RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_srst_v_any", SP_SRST_V, ["block_sp"], ["RDINIT_ANY", "RDSRST_ANY", "RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_srst_v_any_re", SP_SRST_V, ["block_sp"], ["RDINIT_ANY", "RDSRST_ANY", "RDEN", "RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_srst_v_any_re_gated", SP_SRST_V, ["block_sp"], ["RDINIT_ANY", "RDSRST_ANY_RE", "RDEN", "RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_srst_v_any_ce", SP_SRST_V, ["block_sp"], ["RDINIT_ANY", "RDSRST_ANY", "CLKEN", "RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_srst_v_any_ce_gated", SP_SRST_V, ["block_sp"], ["RDINIT_ANY", "RDSRST_ANY_CE", "CLKEN", "RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_srst_v_init", SP_SRST_V, ["block_sp"], ["RDINIT_ANY", "RDSRST_INIT", "RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_srst_v_init_re", SP_SRST_V, ["block_sp"], ["RDINIT_ANY", "RDSRST_INIT", "RDEN", "RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_srst_e_x", SP_SRST_E, ["block_sp"], ["RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_srst_e_x_re", SP_SRST_E, ["block_sp"], ["RDEN", "RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_srst_e_0", SP_SRST_E, ["block_sp"], ["RDINIT_ANY", "RDSRST_0", "RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_srst_e_0_re", SP_SRST_E, ["block_sp"], ["RDINIT_ANY", "RDSRST_0", "RDEN", "RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_srst_e_any", SP_SRST_E, ["block_sp"], ["RDINIT_ANY", "RDSRST_ANY", "RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_srst_e_any_re", SP_SRST_E, ["block_sp"], ["RDINIT_ANY", "RDSRST_ANY", "RDEN", "RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_srst_e_init", SP_SRST_E, ["block_sp"], ["RDINIT_ANY", "RDSRST_INIT", "RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_srst_e_init_re", SP_SRST_E, ["block_sp"], ["RDINIT_ANY", "RDSRST_INIT", "RDEN", "RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_srst_n_x", SP_SRST_N, ["block_sp"], ["RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_srst_n_x_re", SP_SRST_N, ["block_sp"], ["RDEN", "RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_srst_n_0", SP_SRST_N, ["block_sp"], ["RDINIT_ANY", "RDSRST_0", "RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_srst_n_0_re", SP_SRST_N, ["block_sp"], ["RDINIT_ANY", "RDSRST_0", "RDEN", "RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_srst_n_any", SP_SRST_N, ["block_sp"], ["RDINIT_ANY", "RDSRST_ANY", "RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_srst_n_any_re", SP_SRST_N, ["block_sp"], ["RDINIT_ANY", "RDSRST_ANY", "RDEN", "RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_srst_n_init", SP_SRST_N, ["block_sp"], ["RDINIT_ANY", "RDSRST_INIT", "RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_srst_n_init_re", SP_SRST_N, ["block_sp"], ["RDINIT_ANY", "RDSRST_INIT", "RDEN", "RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_srst_gv_x", SP_SRST_GV, ["block_sp"], ["RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_srst_gv_x_re", SP_SRST_GV, ["block_sp"], ["RDEN", "RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_srst_gv_0", SP_SRST_GV, ["block_sp"], ["RDINIT_ANY", "RDSRST_0", "RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_srst_gv_0_re", SP_SRST_GV, ["block_sp"], ["RDINIT_ANY", "RDSRST_0", "RDEN", "RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_srst_gv_any", SP_SRST_GV, ["block_sp"], ["RDINIT_ANY", "RDSRST_ANY", "RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_srst_gv_any_re", SP_SRST_GV, ["block_sp"], ["RDINIT_ANY", "RDSRST_ANY", "RDEN", "RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_srst_gv_any_re_gated", SP_SRST_GV, ["block_sp"], ["RDINIT_ANY", "RDSRST_ANY_RE", "RDEN", "RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_srst_gv_any_ce", SP_SRST_GV, ["block_sp"], ["RDINIT_ANY", "RDSRST_ANY", "CLKEN", "RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_srst_gv_any_ce_gated", SP_SRST_GV, ["block_sp"], ["RDINIT_ANY", "RDSRST_ANY_CE", "CLKEN", "RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_srst_gv_init", SP_SRST_GV, ["block_sp"], ["RDINIT_ANY", "RDSRST_INIT", "RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
    Test("sp_srst_gv_init_re", SP_SRST_GV, ["block_sp"], ["RDINIT_ANY", "RDSRST_INIT", "RDEN", "RDWR_OLD"], {"RAM_BLOCK_SP": 1}),
]

# Byte enables, wrbe_separate
SYNC_ENABLE = """
module top(clk, rwa, rd, wd, we);

localparam ABITS = {abits};
localparam DBITS = {dbits};

input wire clk;
input wire we;
input wire [ABITS-1:0] rwa;
input wire [DBITS-1:0] wd;
output reg [DBITS-1:0] rd;

reg [DBITS-1:0] mem [0:2**ABITS-1];

always @(posedge clk) begin
	if (we)
		mem[rwa] <= wd;
	else
		rd <= mem[rwa];
end

endmodule
"""

for (abits, dbits, sep, defs, cells) in [
	(4, 4, False,	["NO_BYTE"],	{"RAM_WREN": 1}),
	(5, 4, False,	["NO_BYTE"],	{"RAM_WREN": 2}),
	(6, 4, False,	["NO_BYTE"],	{"RAM_WREN": 4}),
	# (4, 4, True,	["NO_BYTE"],	{"RAM_WREN": 1}), # should throw an error
	(3, 8, False,	["NO_BYTE"],	{"RAM_WREN": 2}), # needs two write ports
	(4, 8, False,	["NO_BYTE"],	{"RAM_WREN": 2}),
	(4, 4, False,	["W4_B4"],	{"RAM_WREN": 1}),
	(4, 8, True,	["W4_B4"],	{"RAM_WREN": 2}),
	(4, 8, False,	["W8_B4"],	{"RAM_WREN": 1}),
	(4, 8, True,	["W8_B4"],	{"RAM_WREN": 1}),
	(4, 8, False,	["W8_B8"],	{"RAM_WREN": 1}),
	(4, 8, True,	["W8_B8"],	{"RAM_WREN": 1}),

]:
	name = f"wren_a{abits}d{dbits}_{defs[0]}"
	if (sep):
		defs.append("WRBE_SEPARATE")
		name += "_separate"

	TESTS.append(Test(
		name, SYNC_ENABLE.format(abits=abits, dbits=dbits),
		["wren"], defs, cells
	))

# Write port with byte enables
ENABLES = """
module top(clk, we, be, rwa, wd, rd);

localparam ABITS = {abits};
localparam WBITS = {wbits};
localparam WORDS = {words};

input wire clk;
input wire we;
input wire [WORDS-1:0] be;
input wire [ABITS-1:0] rwa;
input wire [(WBITS*WORDS)-1:0] wd;
output reg [(WBITS*WORDS)-1:0] rd;

reg [(WBITS*WORDS)-1:0] mem [0:2**ABITS-1];

integer i;
always @(posedge clk)
	for (i=0; i<WORDS; i=i+1)
		if (we && be[i])
			mem[rwa][i*WBITS+:WBITS] <= wd[i*WBITS+:WBITS];

always @(posedge clk)
	if (!we)
		rd <= mem[rwa];

endmodule
"""

for (abits, wbits, words, defs, cells) in [
	(4, 2, 8,	["W16_B4"],	{"RAM_WREN": 2}),
	(4, 4, 4,	["W16_B4"],	{"RAM_WREN": 1}),
	(5, 4, 2,	["W16_B4"],	{"RAM_WREN": 1}),
	(5, 4, 4,	["W16_B4"],	{"RAM_WREN": 2}),
	(4, 8, 2,	["W16_B4"],	{"RAM_WREN": 1}),
	(5, 8, 1,	["W16_B4"],	{"RAM_WREN": 1}),
	(5, 8, 2,	["W16_B4"],	{"RAM_WREN": 2}),
	(4,16, 1,	["W16_B4"],	{"RAM_WREN": 1}),
	(4, 4, 2,	["W8_B8"],	{"RAM_WREN": 2}),
	(4, 4, 1,	["W8_B8"],	{"RAM_WREN": 1}),
	(4, 8, 2,	["W8_B8"],	{"RAM_WREN": 2}),
	(3, 8, 2,	["W8_B8"],	{"RAM_WREN": 2}),
	(4, 4, 2,	["W8_B4"],	{"RAM_WREN": 1}),
	(4, 2, 4,	["W8_B4"],	{"RAM_WREN": 2}),
	(4, 4, 4,	["W8_B4"],	{"RAM_WREN": 2}),
	(4, 4, 4,	["W4_B4"],	{"RAM_WREN": 4}),
	(4, 4, 5,	["W4_B4"],	{"RAM_WREN": 5}),

]:
	name = f"wren_a{abits}d{wbits}w{words}_{defs[0]}"
	TESTS.append(Test(
		name, ENABLES.format(abits=abits, wbits=wbits, words=words),
		["wren"], defs, cells
	))

	defs.append("WRBE_SEPARATE")
	name += "_separate"
	TESTS.append(Test(
		name, ENABLES.format(abits=abits, wbits=wbits, words=words),
		["wren"], defs, cells
	))
	
# abits/dbits determination (aka general geometry picking)
GEOMETRIC = """
module top(clk, rwa, rd, wd, we);

localparam ABITS = {abits};
localparam DBITS = {dbits};

input wire clk;
input wire we;
input wire [ABITS-1:0] rwa;
input wire [DBITS-1:0] wd;
output reg [DBITS-1:0] rd;

(* ram_style="block" *)
reg [DBITS-1:0] mem [0:2**ABITS-1];

always @(posedge clk)
	if (we)
		mem[rwa] <= wd;
	else
		rd <= mem[rwa];	

endmodule
"""

for (abits,dbits,	libs,		defs,		cells) in [
	# W64_B8 gives 16 * 64 = 1024 bits of memory with up to 8x8b rw ports
	(  4, 64,	["wren"],	["W64_B8"],	{"RAM_WREN": 1}),
	(  5, 32,	["wren"],	["W64_B8"],	{"RAM_WREN": 1}),
	(  5, 64,	["wren"],	["W64_B8"],	{"RAM_WREN": 2}),
	(  6, 16,	["wren"],	["W64_B8"],	{"RAM_WREN": 1}),
	(  6, 30, 	["wren"], 	["W64_B8"], 	{"RAM_WREN": 2}),
	(  6, 64,	["wren"],	["W64_B8"],	{"RAM_WREN": 4}),
	(  7,  4,	["wren"],	["W64_B8"],	{"RAM_WREN": 1}),
	(  7,  6, 	["wren"], 	["W64_B8"], 	{"RAM_WREN": 1}),
	(  7,  8,	["wren"],	["W64_B8"],	{"RAM_WREN": 1}),
	(  7, 17, 	["wren"], 	["W64_B8"], 	{"RAM_WREN": 3}),
	(  8,  4,	["wren"],	["W64_B8"],	{"RAM_WREN": 2}),
	(  8,  6, 	["wren"], 	["W64_B8"], 	{"RAM_WREN": 2}),
	(  9,  4,	["wren"],	["W64_B8"],	{"RAM_WREN": 4}),
	(  9,  8,	["wren"],	["W64_B8"],	{"RAM_WREN": 4}),
	(  9,  5, 	["wren"], 	["W64_B8"], 	{"RAM_WREN": 4}),
	(  9,  6, 	["wren"], 	["W64_B8"], 	{"RAM_WREN": 4}),
	# 9b1B gives 128 bits of memory with 1 2 or 4 bit read and write ports
	#	or   144 bits with 9 or 18 bit read and write ports
	(  3, 18, 	["9b1B"], 	["INIT_NONE"], 	{"RAM_9b1B": 1}),
	(  4,  4, 	["9b1B"], 	["INIT_NONE"], 	{"RAM_9b1B": 1}),
	(  4, 18, 	["9b1B"], 	["INIT_NONE"], 	{"RAM_9b1B": 2}),
	(  5, 32, 	["9b1B"], 	["INIT_NONE"], 	{"RAM_9b1B": 8}),
	(  6,  4, 	["9b1B"], 	["INIT_NONE"], 	{"RAM_9b1B": 2}),
	(  7, 11, 	["9b1B"], 	["INIT_NONE"], 	{"RAM_9b1B": 11}),
	(  7, 18, 	["9b1B"], 	["INIT_NONE"], 	{"RAM_9b1B": 16}),
	( 11,  1, 	["9b1B"], 	["INIT_NONE"], 	{"RAM_9b1B": 16}),
]:
	name = f"geom_a{abits}d{dbits}_{libs[0]}"
	TESTS.append(Test(
		name, GEOMETRIC.format(abits=abits, dbits=dbits),
		libs, defs, cells
	))

# Mixed width testing
WIDE_SDP = """
module top(rclk, ra, rd, re, rr, wclk, wa, wd, we);

input wire rclk, wclk, re, rr;
input wire [2**({ww}-{bw})-1:0] we;
input wire [{aw}-{rw}+{xw}-1:0] ra;
input wire [{aw}-{ww}+{xw}-1:0] wa;
input wire [2**{ww}-1:0] wd;
output reg [2**{rw}-1:0] rd;

reg mem [0:2**{aw}-1];

initial mem[3] = 0;
initial mem[17] = 1;
initial mem[23] = 0;
initial mem[24] = 1;

integer i, j;
always @(posedge wclk)
    for (i = 0; i < 2**{ww}; i = i + 2**{bw})
        if (we[i >> {bw}])
            for (j = 0; j < 2**{bw}; j = j + 1)
                mem[wa << {ww} | i | j] <= wd[i | j];

always @(posedge rclk)
    if (rr)
        rd <= {sval};
    else if (re)
        for (i = 0; i < 2**{rw}; i = i + 1)
            rd[i] <= mem[ra << {rw} | i];

endmodule
"""

for (aw, rw, ww, bw, xw, sval, cnt) in [
    (6, 1, 1, 1, 1, "2'h1", 1),
    (7, 1, 1, 1, 1, "2'h2", 2),
    (8, 1, 1, 1, 1, "2'h3", 4),
    (6, 0, 0, 0, 0, "2'h0", 1),
    (6, 1, 0, 0, 0, "2'h0", 1),
    (6, 2, 0, 0, 0, "2'h0", 1),
    (6, 3, 0, 0, 0, "2'h0", 1),
    (6, 4, 0, 0, 0, "2'h0", 1),
    (6, 5, 0, 0, 0, "2'h0", 2),
    (6, 0, 1, 0, 0, "2'h0", 2),
    (6, 0, 1, 1, 0, "2'h0", 1),
    (6, 0, 2, 0, 0, "2'h0", 4),
    (6, 0, 2, 2, 0, "2'h0", 1),
    (6, 0, 3, 2, 0, "2'h0", 1),
    (6, 0, 4, 2, 0, "2'h0", 1),
    (6, 0, 5, 2, 0, "2'h0", 2),
    (7, 0, 0, 0, 0, "2'h0", 2),
    (7, 1, 0, 0, 0, "2'h0", 2),
    (7, 2, 0, 0, 0, "2'h0", 2),
    (7, 3, 0, 0, 0, "2'h0", 2),
    (7, 4, 0, 0, 0, "2'h0", 2),
    (7, 5, 0, 0, 0, "2'h0", 2),
    (7, 0, 1, 0, 0, "2'h0", 2),
    (7, 0, 1, 1, 0, "2'h0", 2),
    (7, 0, 2, 0, 0, "2'h0", 4),
    (7, 0, 2, 2, 0, "2'h0", 2),
    (7, 0, 3, 2, 0, "2'h0", 2),
    (7, 0, 4, 2, 0, "2'h0", 2),
    (7, 0, 5, 2, 0, "2'h0", 2),
]:
    TESTS.append(Test(
        f"wide_sdp_a{aw}r{rw}w{ww}b{bw}x{xw}",
        WIDE_SDP.format(aw=aw, rw=rw, ww=ww, bw=bw, xw=xw, sval=sval),
        ["wide_sdp"], [],
        {"RAM_WIDE_SDP": cnt}
    ))

WIDE_SP = """
module top(clk, a, rd, re, rr, wd, we);

input wire clk, re, rr;
input wire [2**({ww}-{bw})-1:0] we;
input wire [{aw}-1:0] a;
input wire [2**{ww}-1:0] wd;
output reg [2**{rw}-1:0] rd;

reg mem [0:2**{aw}-1];

initial mem[3] = 0;
initial mem[17] = 1;
initial mem[23] = 0;
initial mem[24] = 1;

integer i, j;
always @(posedge clk) begin
    for (i = 0; i < 2**{ww}; i = i + 2**{bw})
        if (we[i >> {bw}])
            for (j = 0; j < 2**{bw}; j = j + 1)
                mem[a & ~((1 << {ww}) - 1) | i | j] <= wd[i | j];
    if (rr)
        rd <= {sval};
    else if (re)
        for (i = 0; i < 2**{rw}; i = i + 1)
            rd[i] <= mem[a & ~((1 << {rw}) - 1) | i];
end

endmodule
"""

for (aw, rw, ww, bw, sval, cnt) in [
    (6, 1, 1, 1, "2'h1", 1),
    (7, 1, 1, 1, "2'h2", 2),
    (8, 1, 1, 1, "2'h3", 4),
    (6, 0, 0, 0, "2'h0", 1),
    (6, 1, 0, 0, "2'h0", 1),
    (6, 2, 0, 0, "2'h0", 1),
    (6, 3, 0, 0, "2'h0", 1),
    (6, 4, 0, 0, "2'h0", 1),
    (6, 5, 0, 0, "2'h0", 2),
    (6, 0, 1, 0, "2'h0", 2),
    (6, 0, 1, 1, "2'h0", 1),
    (6, 0, 2, 0, "2'h0", 4),
    (6, 0, 2, 2, "2'h0", 1),
    (6, 0, 3, 2, "2'h0", 1),
    (6, 0, 4, 2, "2'h0", 1),
    (6, 0, 5, 2, "2'h0", 2),
    (7, 0, 0, 0, "2'h0", 2),
    (7, 1, 0, 0, "2'h0", 2),
    (7, 2, 0, 0, "2'h0", 2),
    (7, 3, 0, 0, "2'h0", 2),
    (7, 4, 0, 0, "2'h0", 2),
    (7, 5, 0, 0, "2'h0", 2),
    (7, 0, 1, 0, "2'h0", 2),
    (7, 0, 1, 1, "2'h0", 2),
    (7, 0, 2, 0, "2'h0", 4),
    (7, 0, 2, 2, "2'h0", 2),
    (7, 0, 3, 2, "2'h0", 2),
    (7, 0, 4, 2, "2'h0", 2),
    (7, 0, 5, 2, "2'h0", 2),
]:
    TESTS.append(Test(
        f"wide_sp_mix_a{aw}r{rw}w{ww}b{bw}",
        WIDE_SP.format(aw=aw, rw=rw, ww=ww, bw=bw, sval=sval),
        ["wide_sp"], ["WIDTH_MIX"],
        {"RAM_WIDE_SP": cnt}
    ))

for (aw, rw, ww, bw, sval, cnt) in [
    (6, 1, 1, 1, "2'h1", 1),
    (7, 1, 1, 1, "2'h2", 2),
    (8, 1, 1, 1, "2'h3", 4),
    (6, 0, 0, 0, "2'h0", 1),
    (6, 1, 0, 0, "2'h0", 2),
    (6, 2, 0, 0, "2'h0", 4),
    (6, 3, 0, 0, "2'h0", 4),
    (6, 4, 0, 0, "2'h0", 4),
    (6, 5, 0, 0, "2'h0", 8),
    (6, 0, 1, 0, "2'h0", 2),
    (6, 0, 1, 1, "2'h0", 1),
    (6, 0, 2, 0, "2'h0", 4),
    (6, 0, 2, 2, "2'h0", 1),
    (6, 0, 3, 2, "2'h0", 1),
    (6, 0, 4, 2, "2'h0", 1),
    (6, 0, 5, 2, "2'h0", 2),
    (7, 0, 0, 0, "2'h0", 2),
    (7, 1, 0, 0, "2'h0", 2),
    (7, 2, 0, 0, "2'h0", 4),
    (7, 3, 0, 0, "2'h0", 8),
    (7, 4, 0, 0, "2'h0", 8),
    (7, 5, 0, 0, "2'h0", 8),
    (7, 0, 1, 0, "2'h0", 2),
    (7, 0, 1, 1, "2'h0", 2),
    (7, 0, 2, 0, "2'h0", 4),
    (7, 0, 2, 2, "2'h0", 2),
    (7, 0, 3, 2, "2'h0", 2),
    (7, 0, 4, 2, "2'h0", 2),
    (7, 0, 5, 2, "2'h0", 2),
]:
    TESTS.append(Test(
        f"wide_sp_tied_a{aw}r{rw}w{ww}b{bw}",
        WIDE_SP.format(aw=aw, rw=rw, ww=ww, bw=bw, sval=sval),
        ["wide_sp"], [],
        {"RAM_WIDE_SP": cnt}
    ))

WIDE_RW = """
module top(clk, a, rd, re, wd, we);

input wire clk, re;
input wire [2**({ww}-{bw})-1:0] we;
input wire [{aw}-1:0] a;
input wire [2**{ww}-1:0] wd;
output reg [2**{rw}-1:0] rd;

(* ram_block *)
reg mem [0:2**{aw}-1];

initial mem[3] = 0;
initial mem[17] = 1;
initial mem[23] = 0;
initial mem[24] = 1;

integer i, j;
always @(posedge clk) begin
    for (i = 0; i < 2**{ww}; i = i + 2**{bw})
        if (we[i >> {bw}])
            for (j = 0; j < 2**{bw}; j = j + 1)
                mem[a & ~((1 << {ww}) - 1) | i | j] <= wd[i | j];
    if (re)
        for (i = 0; i < 2**{rw}; i = i + 1)
            rd[i] <= mem[a & ~((1 << {rw}) - 1) | i];
end

endmodule
"""

for (aw, rw, ww, bw, cntww, cntwr) in [
    (6, 1, 1, 1, 2, 1),
    (7, 1, 1, 1, 4, 2),
    (8, 1, 1, 1, 8, 4),
    (6, 0, 0, 0, 4, 2),
    (6, 1, 0, 0, 4, 2),
    (6, 2, 0, 0, 4, 2),
    (6, 3, 0, 0, 8, 2),
    (6, 4, 0, 0, 16, 4),
    (6, 5, 0, 0, 32, 8),
    (6, 0, 1, 0, 4, 2),
    (6, 0, 1, 1, 2, 1),
    (6, 0, 2, 0, 4, 4),
    (6, 0, 2, 2, 1, 2),
    (6, 0, 3, 2, 1, 4),
    (6, 0, 4, 2, 2, 8),
    (6, 0, 5, 2, 4, 16),
    (7, 0, 0, 0, 8, 4),
    (7, 1, 0, 0, 8, 4),
    (7, 2, 0, 0, 8, 4),
    (7, 3, 0, 0, 8, 4),
    (7, 4, 0, 0, 16, 4),
    (7, 5, 0, 0, 32, 8),
    (7, 0, 1, 0, 8, 4),
    (7, 0, 1, 1, 4, 2),
    (7, 0, 2, 0, 8, 4),
    (7, 0, 2, 2, 2, 2),
    (7, 0, 3, 2, 2, 4),
    (7, 0, 4, 2, 2, 8),
    (7, 0, 5, 2, 4, 16),
]:
    TESTS.append(Test(
        f"wide_read_a{aw}r{rw}w{ww}b{bw}",
        WIDE_RW.format(aw=aw, rw=rw, ww=ww, bw=bw),
        ["wide_read"], [],
        {"RAM_WIDE_READ": cntwr}
    ))
    TESTS.append(Test(
        f"wide_write_a{aw}r{rw}w{ww}b{bw}",
        WIDE_RW.format(aw=aw, rw=rw, ww=ww, bw=bw),
        ["wide_write"], [],
        {"RAM_WIDE_WRITE": cntww}
    ))

# Multiple read ports
# 1rw port plus 3 (or 7) r ports
QUAD_PORT = """
module top(clk, rwa, r0a, r1a, r2a, rd, r0d, r1d, r2d, wd, we);

localparam ABITS = {abits};
localparam DBITS = {dbits};

input wire clk;
input wire we;
input wire [ABITS-1:0] rwa;
input wire [ABITS-1:0] r0a;
input wire [ABITS-1:0] r1a;
input wire [ABITS-1:0] r2a;
input wire [DBITS-1:0] wd;
output wire [DBITS-1:0] rd;
output wire [DBITS-1:0] r0d;
output wire [DBITS-1:0] r1d;
output wire [DBITS-1:0] r2d;

reg [DBITS-1:0] mem [0:2**ABITS-1];

always @(posedge clk)
    if (we)
        mem[rwa] <= wd;

assign rd = mem[rwa];
assign r0d = mem[r0a];
assign r1d = mem[r1a];
assign r2d = mem[r2a];

endmodule
"""

for (abits, dbits, cnt) in [
    (2, 2, 1),
    (4, 2, 1),
    (5, 2, 2),
    (4, 4, 2),
    (6, 2, 4),
    (4, 8, 4),
]:
    TESTS.append(Test(
        f"quad_port_a{abits}d{dbits}",
        QUAD_PORT.format(abits=abits, dbits=dbits),
        ["multilut"], ["PORTS_QUAD"],
        {"LUT_MULTI": cnt}
    ))

# Wide asynchronous read port
WIDE_READ = """
module top(clk, we, rwa, wd, rd);

localparam ABITS = {abits};
localparam WBITS = {wbits};
localparam RWORDS = {rwords};

input wire clk;
input wire we;
input wire [ABITS-1:0] rwa;
input wire [WBITS-1:0] wd;
output wire [(WBITS*RWORDS)-1:0] rd;

reg [WBITS-1:0] mem [0:2**ABITS-1];

always @(posedge clk)
	if (we)
		mem[rwa] <= wd;

genvar i;
generate
	for (i = 0; i < RWORDS; i = i + 1)
		assign rd[i*WBITS+:WBITS] = mem[rwa + i];
endgenerate

endmodule
"""

for (abits, wbits, rwords, cntquad, cntoct) in [
	(4, 2, 1, 1, 1),
	(4, 2, 2, 1, 1),
	(4, 2, 3, 1, 1),
	(4, 2, 4, 1, 1),
	(4, 2, 5, 2, 1),
	(4, 2, 6, 2, 1),
	(4, 2, 7, 2, 1), # Write port needs to be duplicated, so only 3 extra read 
	(4, 2, 8, 3, 1), # ports per quad port LUT (i.e. 7 ports in 2, 8 ports in 3)
	(4, 2, 9, 3, 2),
	(4, 4, 1, 2, 2),
	(4, 4, 4, 2, 2),
	(4, 4, 6, 4, 2),
	(4, 4, 9, 6, 4),
	(5, 2, 1, 2, 2),
	(5, 2, 4, 2, 2),
	(5, 2, 9, 6, 4),
]:
	TESTS.append(Test(
		f"wide_quad_a{abits}w{wbits}r{rwords}",
		WIDE_READ.format(abits=abits, wbits=wbits, rwords=rwords),
		["multilut"], ["PORTS_QUAD"],
		{"LUT_MULTI": cntquad}
	))
	TESTS.append(Test(
		f"wide_oct_a{abits}w{wbits}r{rwords}",
		WIDE_READ.format(abits=abits, wbits=wbits, rwords=rwords),
		["multilut"], ["PORTS_OCT"],
		{"LUT_MULTI": cntoct}
	))

# signal priorities & pattern testing
PRIORITY = """
module top(clk, clken, wren, wben, rden, rst, addr, wdata, rdata);

localparam ABITS = {abits};
localparam WBITS = {wbits};
localparam WORDS = {words};

localparam BITS = WBITS * WORDS;

input wire clk, clken;
input wire wren, rden, rst;
input wire [WORDS-1:0] wben;
input wire [ABITS-1:0] addr;
input wire [BITS-1:0] wdata;
output reg [BITS-1:0] rdata;

reg [BITS-1:0] mem [0:2**ABITS-1];

integer i;
always @(posedge clk) begin
{code}
end
endmodule
"""
#reset_gate in ["ungated", "rst", "rden && rst"]
#clk_en in [True, False]
#rdwr in ["nc", "old", "new", "undef", "newdef"]

for (testname, 		reset_gate, 	rdwr,  clk_en, add_logic) in [
	("no_reset", 	"", 		"old", False, 	0),
	("gclken", 	"rst", 		"old", False, 	0),
	("ungated", 	"ungated", 	"old", False, 	1), # muxes wren with rst
	("gclken_ce", 	"rst", 		"old", True, 	3), # AND to simulate CLK_EN
	("grden", 	"rden && rst", 	"old", False, 	1), # selects _clken, simulates _rden
	("grden_ce", 	"rden && rst", 	"old", True, 	4), # both of the above
	("exclwr",	"", 		"nc",  False, 	2), # selects new_only and simulates
	("excl_rst", 	"rst", 		"nc",  False, 	3), # as above, extra gate for rst
	("transwr",	"", 		"new", False, 	0),
	("trans_rst",	"rst", 		"new", False, 	0),
]:
	write = "if (wren) \n\t\tmem[addr] <= wdata;"

	if rdwr == "new":
		read = """if (rden) 
		if (wren)
			rdata <= wdata;
		else
			rdata <= mem[addr];"""
	else:
		read = "if (rden) \n\t\trdata <= mem[addr];"

	if "rst" in reset_gate:
		read = f"if ({reset_gate})\n\t\trdata <= 0; \n\telse {read}"

	if reset_gate == "ungated":
		outer = "if (rst)\n\trdata <= 0;\nelse "
	else:
		outer = ""

	if clk_en:
		outer = f"{outer}if (clken) "

	code = f"""{outer}begin
	{write}
	{"else " if rdwr == "nc" else ""}{read}
end"""

	TESTS.append(Test(
		testname, PRIORITY.format(code=code, abits=4, wbits=8, words=2),
		["block_sp_full"], ["USE_SRST"], 
		{"RAM_BLOCK_SP": 1, "$*": add_logic}
	))

for (testname, 			reset_gate, 	defs, 		rdwr,  add_logic) in [
	("wr_byte",		"", 	["USE_SRST_BLOCKING"],	"old", 0),
	("trans_byte",		"", 	["USE_SRST_BLOCKING"],	"new", 0),
	("wr_rst_byte",		"rst", 	["USE_SRST"],		"old", 2), # expected mux to emulate blocking
	("rst_wr_byte",		"rst", 	["USE_SRST_BLOCKING"],	"old", 2), # should use hardware blocking, doesn't
	("rdenrst_wr_byte", 	"rden && rst", ["USE_SRST"],	"old", 3),
]:
	wordsloop = "for (i=0; i<WORDS; i=i+1)"
	if rdwr == "old":
		read_write = f"""if (rden)
		rdata = mem[addr];
	{wordsloop}
		if (wben[i])
			mem[addr][i] <= wdata[i];"""
	else:
		read_write = f"""{wordsloop}
		if (wben[i]) begin
			mem[addr][i] <= wdata[i];
			rdata[i] <= wdata[i];
		end else
			rdata[i] <= mem[addr][i];"""

	if "rst" in reset_gate:
		reset_rw = f"""if ({reset_gate})
		rdata <= 0;
else begin
	{read_write}
end"""
	else:
		reset_rw = read_write

	if reset_gate == "ungated":
		outer = "if (rst)\n\trdata <= 0;\nelse "
	else:
		outer = ""

	code = f"{outer}\n{reset_rw}"

	TESTS.append(Test(
		testname, PRIORITY.format(code=code, abits=4, wbits=1, words=2),
		["block_sp_full"], defs, 
		{"RAM_BLOCK_SP": 1, "$*": add_logic}
	))
	
ROM_CASE = """
module rom(input clk, input [2:0] addr, {attr}output reg [7:0] data);

always @(posedge clk) begin
	case (addr)
		3'b000: data <= 8'h12;
		3'b001: data <= 8'hAB;
		3'b010: data <= 8'h42;
		3'b011: data <= 8'h23;
		3'b100: data <= 8'h66;
		3'b101: data <= 8'hC0;
		3'b110: data <= 8'h3F;
		3'b111: data <= 8'h95;
	endcase
end

endmodule
"""

TESTS.append(Test("rom_case", ROM_CASE.format(attr=""), ["block_sdp"], [], {"RAM_BLOCK_SDP" : 0}))
TESTS.append(Test("rom_case_block", ROM_CASE.format(attr="(* rom_style = \"block\" *) "), ["block_sdp"], [], {"RAM_BLOCK_SDP" : 1}))

with open("run-test.mk", "w") as mf:
    mf.write("ifneq ($(strip $(SEED)),)\n")
    mf.write("SEEDOPT=-S$(SEED)\n")
    mf.write("endif\n")
    mf.write("all:")
    for t in TESTS:
        mf.write(" " + t.name)
    mf.write("\n")
    mf.write(".PHONY: all\n")


    for t in TESTS:
        with open("t_{}.v".format(t.name), "w") as tf:
            tf.write(t.src)
        with open("t_{}.ys".format(t.name), "w") as sf:
            sf.write("proc\n")
            sf.write("opt\n")
            sf.write("opt -full\n")
            sf.write("memory -nomap\n")
            sf.write("dump\n")
            sf.write("memory_libmap")
            for lib in t.libs:
                sf.write(" -lib ../memlib_{}.txt".format(lib))
            for d in t.defs:
                sf.write(" -D {}".format(d))
            sf.write("\n")
            sf.write("memory_map\n")
            for k, v in t.cells.items():
                if isinstance(v, tuple):
                    (cc, ca) = v
                    sf.write("select -assert-count {} t:{}\n".format(cc, k))
                    for kk, vv in ca.items():
                        sf.write("select -assert-count {} t:{} r:{}={} %i\n".format(cc, k, kk, vv))
                else:
                    sf.write("select -assert-count {} t:{}\n".format(v, k))
        mf.write("{}:\n".format(t.name))
        mf.write("\t@../tools/autotest.sh -G -j $(SEEDOPT) $(EXTRA_FLAGS) -p 'script ../t_{}.ys'".format(t.name))
        for lib in t.libs:
            mf.write(" -l memlib_{}.v".format(lib))
        mf.write(" t_{}.v || (cat t_{}.err; exit 1)\n".format(t.name, t.name))
        mf.write(".PHONY: {}\n".format(t.name))
