module top
(
    input  I0,I1,I2,I3,
    output B1,B2,B3,B4,B5,B6,B7,B8,B9,B10
);
    assign B1 =   I0 &  I1;
    assign B2 =   I0 |  I1;
    assign B3 =   I0 ~& I1;
    assign B4 =   I0 ~| I1;
    assign B5 =   I0 ^  I1;
    assign B6 =   I0 ~^ I1;
    assign B7 =  ~I0;
    assign B8 =   I0;
    assign B9 =   {I1,I0} && {I3,I3};
    assign B10 =  {I1,I0} || {I3,I2};
endmodule
