module producer(
    output logic [3:0] out
);
    assign out = 4'hA;
endmodule

module top(
    output logic [3:0] out0, out1
);
    logic [3:0] v[1:0];
    producer p0(v[0]);
    producer p1({v[1]});
    assign out0 = v[0];
    assign out1 = v[1];
endmodule
