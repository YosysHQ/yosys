
// a simple test case extracted from systemcaes (as included in iwls2005)
// this design has latches (or logic loops) for the two temp variables.
// this latches (or logic loops) must be removed in the final synthesis results

module aes(
	// inputs
	input [3:0] addroundkey_data_i,
	input [3:0] addroundkey_data_reg,
	input [3:0] addroundkey_round,
	input [3:0] key_i,
	input [3:0] keysched_new_key_o,
	input [3:0] round,
	input addroundkey_start_i,
	input keysched_ready_o,

	// outputs
	output reg [3:0] keysched_last_key_i,
	output reg [3:0] keysched_round_i,
	output reg [3:0] next_addroundkey_data_reg,
	output reg [3:0] next_addroundkey_round,
	output reg [3:0] round_data_var,
	output reg keysched_start_i,
	output reg next_addroundkey_ready_o
);

// temp variables
reg [3:0] data_var;
reg [3:0] round_key_var;

always @*
begin
	keysched_start_i = 0;
	keysched_round_i = addroundkey_round;
	round_data_var = addroundkey_data_reg;
	next_addroundkey_data_reg = addroundkey_data_reg;
	next_addroundkey_ready_o = 0;
	next_addroundkey_round = addroundkey_round;

	if (addroundkey_round == 1 || addroundkey_round == 0)
		keysched_last_key_i = key_i;
	else
		keysched_last_key_i = keysched_new_key_o;

	if (round == 0 && addroundkey_start_i)
	begin
		data_var = addroundkey_data_i;
		round_key_var = key_i;
		round_data_var = round_key_var ^ data_var;
		next_addroundkey_data_reg = round_data_var;
		next_addroundkey_ready_o = 1;
	end
	else if (addroundkey_start_i && round != 0)
	begin
		keysched_last_key_i = key_i;
		keysched_start_i = 1;
		keysched_round_i = 1;
		next_addroundkey_round = 1;
	end
	else if (addroundkey_round != round && keysched_ready_o)
	begin
		next_addroundkey_round = addroundkey_round + 1;
		keysched_last_key_i = keysched_new_key_o;
		keysched_start_i = 1;
		keysched_round_i = addroundkey_round + 1;
	end
	else if (addroundkey_round == round && keysched_ready_o)
	begin
		data_var = addroundkey_data_i;
		round_key_var = keysched_new_key_o;
		round_data_var = round_key_var ^ data_var;
		next_addroundkey_data_reg = round_data_var;
		next_addroundkey_ready_o = 1;
		next_addroundkey_round = 0;
	end
end

endmodule

