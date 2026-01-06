module gate(
    (* nowrshmsk = `ALT *)
    output reg [`LEFT:`RIGHT] out_u, out_s,
    input wire data,
    input wire [1:0] sel1, sel2
);
always @* begin
    out_u = 'x;
    out_s = 'x;
    case (`SPAN)
    1: begin
        out_u[sel1*sel2] = data;
        out_s[$signed(sel1*sel2)] = data;
    end
    2: begin
        out_u[sel1*sel2+:2] = {data, data};
        out_s[$signed(sel1*sel2)+:2] = {data, data};
    end
    3: begin
        out_u[sel1*sel2+:3] = {data, data, data};
        out_s[$signed(sel1*sel2)+:3] = {data, data, data};
    end
    4: begin
        out_u[sel1*sel2+:4] = {data, data, data, data};
        out_s[$signed(sel1*sel2)+:4] = {data, data, data, data};
    end
    endcase
end
endmodule

module gold(
    output reg [`LEFT:`RIGHT] out_u, out_s,
    input wire data,
    input wire [1:0] sel1, sel2
);
task set;
    input integer a, b;
    localparam LOW = `LEFT > `RIGHT ? `RIGHT : `LEFT;
    localparam HIGH = `LEFT > `RIGHT ? `LEFT : `RIGHT;
    if (LOW <= a && a <= HIGH)
        out_u[a] = data;
    if (LOW <= b && b <= HIGH)
        out_s[b] = data;
endtask
always @* begin
    out_u = 'x;
    out_s = 'x;
    case (sel1*sel2)
        2'b00: set(0, 0);
        2'b01: set(1, 1);
        2'b10: set(2, -2);
        2'b11: set(3, -1);
    endcase
    if (`SPAN >= 2)
        case (sel1*sel2)
            2'b00: set(1, 1);
            2'b01: set(2, 2);
            2'b10: set(3, -1);
            2'b11: set(4, 0);
        endcase
    if (`SPAN >= 3)
        case (sel1*sel2)
            2'b00: set(2, 2);
            2'b01: set(3, 3);
            2'b10: set(4, 0);
            2'b11: set(5, 1);
        endcase
    if (`SPAN >= 4)
        case (sel1*sel2)
            2'b00: set(3, 3);
            2'b01: set(4, 4);
            2'b10: set(5, 1);
            2'b11: set(6, 2);
        endcase
end
endmodule
