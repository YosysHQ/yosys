module top;

	typedef struct packed {
		byte a,b,c,d;
	} byte4_t;

	typedef union packed {
		int	x;
		byte4_t	y;
	} w_t;

	w_t w;

	assign w.x = 'h42;
	always_comb begin
		assert(w.y.d == 8'h42);
	end

	typedef logic[4:0] reg_addr_t;
	typedef logic[6:0] opcode_t;

	typedef struct packed {
		bit [6:0]  func7;
		reg_addr_t rs2;
		reg_addr_t rs1;
		bit [2:0]  func3;
		reg_addr_t rd;
		opcode_t   opcode;
	} R_t;

	typedef struct packed {
		bit[11:0]  imm;
		reg_addr_t rs1;
		bit[2:0]   func3;
		reg_addr_t rd;
		opcode_t   opcode;
	} I_t;

	typedef struct packed {
		bit[19:0]  imm;
		reg_addr_t rd;
		opcode_t   opcode;
	} U_t;

	typedef union packed {
		R_t	r;
		I_t	i;
		U_t	u;
	} instruction_t;

	typedef struct packed {
		instruction_t	ir;
		logic [3:0]     state;
	} s_t;

	instruction_t ir1;
	s_t s1;

	assign ir1 = 32'h0AA01EB7;          //	lui t4,0xAA01
	assign s1.ir = ir1;
	assign s1.state = '1;

	always_comb begin
		assert(ir1.u.opcode == 'h37);
		assert(ir1.r.opcode == 'h37);
		assert(ir1.u.rd == 'd29);
		assert(ir1.r.rd == 'd29);
		assert(ir1.u.imm == 'hAA01);
		assert(s1.ir.u.opcode == 'h37);
		assert(s1.ir.r.opcode == 'h37);
		assert(s1.ir.u.rd == 'd29);
		assert(s1.ir.r.rd == 'd29);
		assert(s1.ir.u.imm == 'hAA01);
		assert(s1.state == 4'b1111);
	end

	union packed {
		int word;
		struct packed {
			byte a, b, c, d;
		} byte4;
	} u;
	assign u.word = 'h42;
	always_comb begin
		assert(u.byte4.d == 'h42);
	end

endmodule
