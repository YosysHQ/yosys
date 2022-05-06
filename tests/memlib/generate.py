# TODO:

# - memory initialization
# - clock polarity combinations
# - CE/srst/rdwr/be interactions
# - priority logic
# - byte enables, wrbe_separate
# - duplication for read ports
# - abits/dbits determination
# - mixed width
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
