module producer(
    output logic [3:0] out
);
    assign out = 4'hA;
endmodule

module top(
    output logic [3:0] out
);
    logic [3:0] v[0:0];
    producer p(v[0]);
    assign out = v[0];
endmodule
