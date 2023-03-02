module range_shift_mask(
    input logic [2:0] addr_i,
    input logic [7:0] data_i,
    input logic [2:0] addr_o,
    output logic [7:0] data_o
);
    (* nowrshmsk = 0 *)
    struct packed {
        logic [7:0] msb;
        logic [0:3][7:0] data;
        logic [7:0] lsb;
    } s;

    always_comb begin
        s = '1;
        s.data[addr_i] = data_i;
        data_o = s.data[addr_o];
    end
endmodule

module range_case(
    input logic [2:0] addr_i,
    input logic [7:0] data_i,
    input logic [2:0] addr_o,
    output logic [7:0] data_o
);
    (* nowrshmsk = 1 *)
    struct packed {
        logic [7:0] msb;
        logic [0:3][7:0] data;
        logic [7:0] lsb;
    } s;

    always_comb begin
        s = '1;
        s.data[addr_i] = data_i;
        data_o = s.data[addr_o];
    end
endmodule

module top;
    logic [7:0] data_shift_mask1;
    range_shift_mask range_shift_mask1(3'd1, 8'h7e, 3'd1, data_shift_mask1);
    logic [7:0] data_shift_mask2;
    range_shift_mask range_shift_mask2(3'd1, 8'h7e, 3'd2, data_shift_mask2);
    logic [7:0] data_shift_mask3;
    range_shift_mask range_shift_mask3(3'd1, 8'h7e, 3'd4, data_shift_mask3);

    always_comb begin
        assert(data_shift_mask1 === 8'h7e);
        assert(data_shift_mask2 === 8'hff);
        assert(data_shift_mask3 === 8'hxx);
    end

    logic [7:0] data_case1;
    range_case range_case1(3'd1, 8'h7e, 3'd1, data_case1);
    logic [7:0] data_case2;
    range_case range_case2(3'd1, 8'h7e, 3'd2, data_case2);
    logic [7:0] data_case3;
    range_case range_case3(3'd1, 8'h7e, 3'd4, data_case3);

    always_comb begin
        assert(data_case1 === 8'h7e);
        assert(data_case2 === 8'hff);
        assert(data_case3 === 8'hxx);
    end
endmodule
