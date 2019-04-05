module GP_DFFS(input D, CLK, nSET, output reg Q);
	parameter [0:0] INIT = 1'bx;
	GP_DFFSR #(
		.INIT(INIT),
		.SRMODE(1'b1),
	) _TECHMAP_REPLACE_ (
		.D(D),
		.CLK(CLK),
		.nSR(nSET),
		.Q(Q)
	);
endmodule

module GP_DFFR(input D, CLK, nRST, output reg Q);
	parameter [0:0] INIT = 1'bx;
	GP_DFFSR #(
		.INIT(INIT),
		.SRMODE(1'b0),
	) _TECHMAP_REPLACE_ (
		.D(D),
		.CLK(CLK),
		.nSR(nRST),
		.Q(Q)
	);
endmodule

module GP_DFFSI(input D, CLK, nSET, output reg nQ);
	parameter [0:0] INIT = 1'bx;
	GP_DFFSRI #(
		.INIT(INIT),
		.SRMODE(1'b1),
	) _TECHMAP_REPLACE_ (
		.D(D),
		.CLK(CLK),
		.nSR(nSET),
		.nQ(nQ)
	);
endmodule

module GP_DFFRI(input D, CLK, nRST, output reg nQ);
	parameter [0:0] INIT = 1'bx;
	GP_DFFSRI #(
		.INIT(INIT),
		.SRMODE(1'b0),
	) _TECHMAP_REPLACE_ (
		.D(D),
		.CLK(CLK),
		.nSR(nRST),
		.nQ(nQ)
	);
endmodule

module GP_DLATCHS(input D, nCLK, nSET, output reg Q);
	parameter [0:0] INIT = 1'bx;
	GP_DLATCHSR #(
		.INIT(INIT),
		.SRMODE(1'b1),
	) _TECHMAP_REPLACE_ (
		.D(D),
		.nCLK(nCLK),
		.nSR(nSET),
		.Q(Q)
	);
endmodule

module GP_DLATCHR(input D, nCLK, nRST, output reg Q);
	parameter [0:0] INIT = 1'bx;
	GP_DLATCHSR #(
		.INIT(INIT),
		.SRMODE(1'b0),
	) _TECHMAP_REPLACE_ (
		.D(D),
		.nCLK(nCLK),
		.nSR(nRST),
		.Q(Q)
	);
endmodule

module GP_DLATCHSI(input D, nCLK, nSET, output reg nQ);
	parameter [0:0] INIT = 1'bx;
	GP_DLATCHSRI #(
		.INIT(INIT),
		.SRMODE(1'b1),
	) _TECHMAP_REPLACE_ (
		.D(D),
		.nCLK(nCLK),
		.nSR(nSET),
		.nQ(nQ)
	);
endmodule

module GP_DLATCHRI(input D, nCLK, nRST, output reg nQ);
	parameter [0:0] INIT = 1'bx;
	GP_DLATCHSRI #(
		.INIT(INIT),
		.SRMODE(1'b0),
	) _TECHMAP_REPLACE_ (
		.D(D),
		.nCLK(nCLK),
		.nSR(nRST),
		.nQ(nQ)
	);
endmodule

module GP_OBUFT(input IN, input OE, output OUT);
	GP_IOBUF _TECHMAP_REPLACE_ (
		.IN(IN),
		.OE(OE),
		.IO(OUT),
		.OUT()
	);
endmodule

module \$lut (A, Y);
	parameter WIDTH = 0;
	parameter LUT = 0;

	input [WIDTH-1:0] A;
	output Y;

	generate
		if (WIDTH == 1) begin
		if(LUT == 2'b01) begin
			GP_INV _TECHMAP_REPLACE_ (.OUT(Y), .IN(A[0]) );
		end
		else begin
			GP_2LUT #(.INIT({2'b00, LUT})) _TECHMAP_REPLACE_ (.OUT(Y),
				.IN0(A[0]), .IN1(1'b0));
		end
		end else
		if (WIDTH == 2) begin
			GP_2LUT #(.INIT(LUT)) _TECHMAP_REPLACE_ (.OUT(Y),
				.IN0(A[0]), .IN1(A[1]));
		end else
		if (WIDTH == 3) begin
			GP_3LUT #(.INIT(LUT)) _TECHMAP_REPLACE_ (.OUT(Y),
				.IN0(A[0]), .IN1(A[1]), .IN2(A[2]));
		end else
		if (WIDTH == 4) begin
			GP_4LUT #(.INIT(LUT)) _TECHMAP_REPLACE_ (.OUT(Y),
				.IN0(A[0]), .IN1(A[1]), .IN2(A[2]), .IN3(A[3]));
		end else begin
			wire _TECHMAP_FAIL_ = 1;
		end
	endgenerate
endmodule

module \$__COUNT_ (CE, CLK, OUT, POUT, RST, UP);

	input wire CE;
	input wire CLK;
	output reg OUT;
	output reg[WIDTH-1:0] POUT;
	input wire RST;
	input wire UP;

	parameter COUNT_TO = 1;
	parameter RESET_MODE = "RISING";
	parameter RESET_TO_MAX = 0;
	parameter HAS_POUT = 0;
	parameter HAS_CE = 0;
	parameter WIDTH = 8;
	parameter DIRECTION = "DOWN";

	//If we have a DIRECTION other than DOWN fail... GP_COUNTx_ADV is not supported yet
	if(DIRECTION != "DOWN") begin
		initial begin
			$display("ERROR: \$__COUNT_ support for GP_COUNTx_ADV is not yet implemented. This counter should never have been extracted (bug in extract_counter pass?).");
			$finish;
		end
	end

	//If counter is more than 14 bits wide, complain (also shouldn't happen)
	else if(WIDTH > 14) begin
		initial begin
			$display("ERROR: \$__COUNT_ support for cascaded counters is not yet implemented. This counter should never have been extracted (bug in extract_counter pass?).");
			$finish;
		end
	end

	//If counter is more than 8 bits wide and has parallel output, we have a problem
	else if(WIDTH > 8 && HAS_POUT) begin
		initial begin
			$display("ERROR: \$__COUNT_ support for 9-14 bit counters with parallel output is not yet implemented. This counter should never have been extracted (bug in extract_counter pass?).");
			$finish;
		end
	end

	//Looks like a legal counter! Do something with it
	else if(WIDTH <= 8) begin
		if(HAS_CE) begin
			wire ce_not;
			GP_INV ceinv(
				.IN(CE),
				.OUT(ce_not)
			);
			GP_COUNT8_ADV #(
				.COUNT_TO(COUNT_TO),
				.RESET_MODE(RESET_MODE),
				.RESET_VALUE(RESET_TO_MAX ? "COUNT_TO" : "ZERO"),
				.CLKIN_DIVIDE(1)
			) _TECHMAP_REPLACE_ (
				.CLK(CLK),
				.RST(RST),
				.OUT(OUT),
				.UP(1'b0),		//always count down for now
				.KEEP(ce_not),
				.POUT(POUT)
			);
		end
		else begin
			GP_COUNT8 #(
				.COUNT_TO(COUNT_TO),
				.RESET_MODE(RESET_MODE),
				.CLKIN_DIVIDE(1)
			) _TECHMAP_REPLACE_ (
				.CLK(CLK),
				.RST(RST),
				.OUT(OUT),
				.POUT(POUT)
			);
		end
	end

	else begin
		if(HAS_CE) begin
			wire ce_not;
			GP_INV ceinv(
				.IN(CE),
				.OUT(ce_not)
			);
			GP_COUNT14_ADV #(
				.COUNT_TO(COUNT_TO),
				.RESET_MODE(RESET_TO_MAX ? "COUNT_TO" : "ZERO"),
				.RESET_VALUE("COUNT_TO"),
				.CLKIN_DIVIDE(1)
			) _TECHMAP_REPLACE_ (
				.CLK(CLK),
				.RST(RST),
				.OUT(OUT),
				.UP(1'b0),		//always count down for now
				.KEEP(ce_not),
				.POUT(POUT)
			);
		end
		else begin
			GP_COUNT14 #(
				.COUNT_TO(COUNT_TO),
				.RESET_MODE(RESET_MODE),
				.CLKIN_DIVIDE(1)
			) _TECHMAP_REPLACE_ (
				.CLK(CLK),
				.RST(RST),
				.OUT(OUT)
			);
		end
	end

endmodule
