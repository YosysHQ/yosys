module producer(
    output logic [3:0] out
);
    assign out = 4'hA;
endmodule

module top(
    output logic [3:0] out0, out1, out2, out3
);
    logic [3:0] v[1:0];
    logic [1:0] u[1:0];
    logic [1:0] t[1:0];
    producer p0(v[0]);
    producer p1({v[1]});
    producer p2({u[1], u[0]});
    producer p3({{t[1]}, {t[0]}});
    assign out0 = v[0];
    assign out1 = v[1];
    assign out2 = {u[1], u[0]};
    assign out3 = {t[1], t[0]};
endmodule
