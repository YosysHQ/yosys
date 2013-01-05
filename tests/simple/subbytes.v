
// test taken from systemcaes from iwls2005

module subbytes_00(clk, reset, start_i, decrypt_i, data_i, ready_o, data_o, sbox_data_o, sbox_data_i, sbox_decrypt_o);

input clk;
input reset;
input start_i;
input decrypt_i;
input [31:0] data_i;
output ready_o;
output [31:0] data_o;
output [7:0] sbox_data_o;
input [7:0] sbox_data_i;
output sbox_decrypt_o;

reg ready_o;
reg [31:0] data_o;
reg [7:0] sbox_data_o;
reg sbox_decrypt_o;

reg [1:0] state;
reg [1:0] next_state;
reg [31:0] data_reg;
reg [31:0] next_data_reg;
reg next_ready_o;

always @(posedge clk or negedge reset)
begin
	if (!reset) begin
		data_reg = 0;
		state = 0;
		ready_o = 0;
	end else begin
		data_reg = next_data_reg;
		state = next_state;
		ready_o = next_ready_o;
	end
end

reg [31:0] data_i_var, data_reg_128;
reg [7:0] data_array [3:0];
reg [7:0] data_reg_var [3:0];

always @(decrypt_i or start_i or state or data_i or sbox_data_i or data_reg)
begin
	data_i_var = data_i;

	data_array[0] = data_i_var[ 31: 24];
	data_array[1] = data_i_var[ 23: 16];
	data_array[2] = data_i_var[ 15:  8];
	data_array[3] = data_i_var[  7:  0];

	data_reg_var[0] = data_reg[ 31: 24];
	data_reg_var[1] = data_reg[ 23: 16];
	data_reg_var[2] = data_reg[ 15:  8];
	data_reg_var[3] = data_reg[  7:  0];

	sbox_decrypt_o = decrypt_i;
	sbox_data_o = data_array[state];
	next_state = state;
	next_data_reg = data_reg;

	next_ready_o = 0;
	data_o = data_reg;

	if (state) begin
		if (start_i) begin
			next_state = 1;
		end
	end else begin
		data_reg_var[state] = sbox_data_i;
		data_reg_128[ 31: 24] = data_reg_var[0];
		data_reg_128[ 23: 16] = data_reg_var[1];
		data_reg_128[ 15:  8] = data_reg_var[2];
		data_reg_128[  7:  0] = data_reg_var[3];
		next_data_reg = data_reg_128;
		next_state = state + 1;
	end
end

endmodule
