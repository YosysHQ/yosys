module IBUF(input I, output O);
    assign O = I;
endmodule

module IOBUFE(input I, input E, output O, inout IO);
    assign O = IO;
    assign IO = E ? I : 1'bz;
endmodule

module ANDTERM(IN, IN_B, OUT);
    parameter TRUE_INP = 0;
    parameter COMP_INP = 0;

    input [TRUE_INP-1:0] IN;
    input [COMP_INP-1:0] IN_B;
    output reg OUT;

    integer i;

    always @(*) begin
        OUT = 1;
        for (i = 0; i < TRUE_INP; i=i+1)
            OUT = OUT & IN[i];
        for (i = 0; i < COMP_INP; i=i+1)
            OUT = OUT & ~IN_B[i];
    end
endmodule

module ORTERM(IN, OUT);
    parameter WIDTH = 0;

    input [WIDTH-1:0] IN;
    output reg OUT;

    integer i;

    always @(*) begin
        OUT = 0;
        for (i = 0; i < WIDTH; i=i+1) begin
            OUT = OUT | IN[i];
        end
    end
endmodule

module MACROCELL_XOR(IN_PTC, IN_ORTERM, OUT);
    parameter INVERT_OUT = 0;

    input IN_PTC;
    input IN_ORTERM;
    output wire OUT;

    wire xor_intermed;

    assign OUT = INVERT_OUT ? ~xor_intermed : xor_intermed;
    assign xor_intermed = IN_ORTERM ^ IN_PTC;
endmodule

module FDCP (C, PRE, CLR, D, Q);
    parameter INIT = 0;

    input C, PRE, CLR, D;
    output reg Q;

    initial begin
        Q <= INIT;
    end

    always @(posedge C, posedge PRE, posedge CLR) begin
        if (CLR == 1)
            Q <= 0;
        else if (PRE == 1)
            Q <= 1;
        else
            Q <= D;
    end
endmodule

module FDCP_N (C, PRE, CLR, D, Q);
    parameter INIT = 0;

    input C, PRE, CLR, D;
    output reg Q;

    initial begin
        Q <= INIT;
    end

    always @(negedge C, posedge PRE, posedge CLR) begin
        if (CLR == 1)
            Q <= 0;
        else if (PRE == 1)
            Q <= 1;
        else
            Q <= D;
    end
endmodule

module LDCP (G, PRE, CLR, D, Q);
    parameter INIT = 0;

    input G, PRE, CLR, D;
    output reg Q;

    initial begin
        Q <= INIT;
    end

    always @* begin
        if (CLR == 1)
            Q <= 0;
        else if (G == 1)
            Q <= D;
        else if (PRE == 1)
            Q <= 1;
    end
endmodule

module LDCP_N (G, PRE, CLR, D, Q);
    parameter INIT = 0;

    input G, PRE, CLR, D;
    output reg Q;

    initial begin
        Q <= INIT;
    end

    always @* begin
        if (CLR == 1)
            Q <= 0;
        else if (G == 0)
            Q <= D;
        else if (PRE == 1)
            Q <= 1;
    end
endmodule

module BUFG(I, O);
    input I;
    output O;

    assign O = I;
endmodule

module BUFGSR(I, O);
    parameter INVERT = 0;

    input I;
    output O;

    assign O = INVERT ? ~I : I;
endmodule

module BUFGTS(I, O);
    parameter INVERT = 0;

    input I;
    output O;

    assign O = INVERT ? ~I : I;
endmodule

module FDDCP (C, PRE, CLR, D, Q);
    parameter INIT = 0;

    input C, PRE, CLR, D;
    output reg Q;

    initial begin
        Q <= INIT;
    end

    always @(posedge C, negedge C, posedge PRE, posedge CLR) begin
        if (CLR == 1)
            Q <= 0;
        else if (PRE == 1)
            Q <= 1;
        else
            Q <= D;
    end
endmodule

module FTCP (C, PRE, CLR, T, Q);
    parameter INIT = 0;

    input C, PRE, CLR, T;
    output wire Q;
    reg Q_;

    initial begin
        Q_ <= INIT;
    end

    always @(posedge C, posedge PRE, posedge CLR) begin
        if (CLR == 1)
            Q_ <= 0;
        else if (PRE == 1)
            Q_ <= 1;
        else if (T == 1)
            Q_ <= ~Q_;
    end

    assign Q = Q_;
endmodule

module FTCP_N (C, PRE, CLR, T, Q);
    parameter INIT = 0;

    input C, PRE, CLR, T;
    output wire Q;
    reg Q_;

    initial begin
        Q_ <= INIT;
    end

    always @(negedge C, posedge PRE, posedge CLR) begin
        if (CLR == 1)
            Q_ <= 0;
        else if (PRE == 1)
            Q_ <= 1;
        else if (T == 1)
            Q_ <= ~Q_;
    end

    assign Q = Q_;
endmodule

module FTDCP (C, PRE, CLR, T, Q);
    parameter INIT = 0;

    input C, PRE, CLR, T;
    output wire Q;
    reg Q_;

    initial begin
        Q_ <= INIT;
    end

    always @(posedge C, negedge C, posedge PRE, posedge CLR) begin
        if (CLR == 1)
            Q_ <= 0;
        else if (PRE == 1)
            Q_ <= 1;
        else if (T == 1)
            Q_ <= ~Q_;
    end

    assign Q = Q_;
endmodule

module FDCPE (C, PRE, CLR, D, Q, CE);
    parameter INIT = 0;

    input C, PRE, CLR, D, CE;
    output reg Q;

    initial begin
        Q <= INIT;
    end

    always @(posedge C, posedge PRE, posedge CLR) begin
        if (CLR == 1)
            Q <= 0;
        else if (PRE == 1)
            Q <= 1;
        else if (CE == 1)
            Q <= D;
    end
endmodule

module FDCPE_N (C, PRE, CLR, D, Q, CE);
    parameter INIT = 0;

    input C, PRE, CLR, D, CE;
    output reg Q;

    initial begin
        Q <= INIT;
    end

    always @(negedge C, posedge PRE, posedge CLR) begin
        if (CLR == 1)
            Q <= 0;
        else if (PRE == 1)
            Q <= 1;
        else if (CE == 1)
            Q <= D;
    end
endmodule

module FDDCPE (C, PRE, CLR, D, Q, CE);
    parameter INIT = 0;

    input C, PRE, CLR, D, CE;
    output reg Q;

    initial begin
        Q <= INIT;
    end

    always @(posedge C, negedge C, posedge PRE, posedge CLR) begin
        if (CLR == 1)
            Q <= 0;
        else if (PRE == 1)
            Q <= 1;
        else if (CE == 1)
            Q <= D;
    end
endmodule
