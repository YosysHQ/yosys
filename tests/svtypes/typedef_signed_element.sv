module top;
	typedef logic signed [4:1] operand_t;
	typedef operand_t [1:0] pair_t;

	operand_t [1:0] operands;
	operand_t [1:0][1:0] grid;
	operand_t [1:0] memory [1];
	pair_t [0:0] pairs;
	logic [4:1] words [1];
	logic index;
	operand_t [1:0] written;
	operand_t [1:0] accumulated;
	operand_t [1:0] concatenated;
	struct packed { operand_t [1:0] operands; operand_t operand; } structure, written_structure;

	function automatic logic [7:0] widen(operand_t value);
		widen = value;
	endfunction

	function automatic logic [7:0] widen_local_element();
		operand_t [1:0] local_operands;
		local_operands = '1;
		widen_local_element = local_operands[0];
	endfunction
	localparam logic [7:0] constant_function_result = widen_local_element();

	assign operands = '1;
	assign grid = '1;
	assign memory[0] = '1;
	assign pairs = '1;
	assign words[0] = '1;
	assign index = 1;
	assign structure = '1;
	always_comb begin
		written = '0;
		written[index] = '1;
		written_structure = '0;
		written_structure.operands[index] = '1;
		accumulated = '0;
		accumulated[0] += operands[0];
		{concatenated[1], concatenated[0]} = 8'hf0;
	end

	// A signed operand is sign-extended to the constant's width; an unsigned one is zero-extended.
	always_comb begin
		assert(operands[0] == 8'shff);
		assert(grid[1][0] == 8'shff);
		assert(memory[0][0] == 8'shff);
		assert(written[index] == 8'shff);
		assert(operands == 16'sh00ff);
		assert(operands[1:1] == 8'sh0f);
		assert(operands[0][4] == 8'sh01);
		assert(grid[0] == 16'sh00ff);
		assert(grid[1][1:1] == 8'sh0f);
		assert(pairs[0] == 16'sh00ff);
		assert(pairs[0][1] == 8'shff);
		assert(words[0] == 8'sh0f);
		assert($left(operands[0]) == 4);
		assert(accumulated[0] == 8'shff);
		assert(concatenated[1] == 8'shff);
		assert(widen(operands[0]) == 8'shff);
		assert(structure.operands[0] == 8'shff);
		assert(structure.operands == 16'sh00ff);
		assert(structure.operands[1:1] == 8'sh0f);
		assert(structure.operands[0][4] == 8'sh01);
		assert(written_structure.operands[index] == 8'shff);
		assert(structure.operand == 8'shff);
		assert(structure.operand[4:3] == 8'sh03);
		assert(structure.operand[4] == 8'sh01);
		assert($left(structure.operand) == 4);
		assert($left($signed(operands)) == 7);
		assert(constant_function_result == 8'hff);
	end
endmodule
