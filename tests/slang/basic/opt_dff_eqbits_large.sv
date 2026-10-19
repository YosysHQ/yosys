module test_case (
	input wire clk,
	input wire rst_n,
	input wire [3:0] chan_0_data,
	input wire chan_0_vld,
	input wire chan_1_rdy,
	output wire chan_0_rdy,
	output wire [207:0] chan_1_data,
	output wire chan_1_vld,
	output wire idle
);
	wire [12:0] state_init[0:15];
	assign state_init[0]  = 13'h0000;
	assign state_init[1]  = 13'h0000;
	assign state_init[2]  = 13'h0000;
	assign state_init[3]  = 13'h0000;
	assign state_init[4]  = 13'h0000;
	assign state_init[5]  = 13'h0000;
	assign state_init[6]  = 13'h0000;
	assign state_init[7]  = 13'h0000;
	assign state_init[8]  = 13'h0000;
	assign state_init[9]  = 13'h0000;
	assign state_init[10] = 13'h0000;
	assign state_init[11] = 13'h0000;
	assign state_init[12] = 13'h0000;
	assign state_init[13] = 13'h0000;
	assign state_init[14] = 13'h0000;
	assign state_init[15] = 13'h0000;

	wire [12:0] ch1_init[0:15];
	assign ch1_init[0]  = 13'h0000;
	assign ch1_init[1]  = 13'h0000;
	assign ch1_init[2]  = 13'h0000;
	assign ch1_init[3]  = 13'h0000;
	assign ch1_init[4]  = 13'h0000;
	assign ch1_init[5]  = 13'h0000;
	assign ch1_init[6]  = 13'h0000;
	assign ch1_init[7]  = 13'h0000;
	assign ch1_init[8]  = 13'h0000;
	assign ch1_init[9]  = 13'h0000;
	assign ch1_init[10] = 13'h0000;
	assign ch1_init[11] = 13'h0000;
	assign ch1_init[12] = 13'h0000;
	assign ch1_init[13] = 13'h0000;
	assign ch1_init[14] = 13'h0000;
	assign ch1_init[15] = 13'h0000;

	wire [12:0] mask_1fff[0:15];
	assign mask_1fff[0]  = 13'h1fff;
	assign mask_1fff[1]  = 13'h1fff;
	assign mask_1fff[2]  = 13'h1fff;
	assign mask_1fff[3]  = 13'h1fff;
	assign mask_1fff[4]  = 13'h1fff;
	assign mask_1fff[5]  = 13'h1fff;
	assign mask_1fff[6]  = 13'h1fff;
	assign mask_1fff[7]  = 13'h1fff;
	assign mask_1fff[8]  = 13'h1fff;
	assign mask_1fff[9]  = 13'h1fff;
	assign mask_1fff[10] = 13'h1fff;
	assign mask_1fff[11] = 13'h1fff;
	assign mask_1fff[12] = 13'h1fff;
	assign mask_1fff[13] = 13'h1fff;
	assign mask_1fff[14] = 13'h1fff;
	assign mask_1fff[15] = 13'h1fff;

	reg [12:0] state_array[0:15];
	reg [3:0] ch0_in_buf;
	reg ch0_in_buf_vld;
	reg [12:0] ch1_out_buf[0:15];
	reg ch1_out_buf_vld;
	reg stg1_vld;

	wire ch1_not_vld;
	wire [3:0] ch0_sel_data;
	wire ch0_is_vld;
	wire ch1_vld_we;
	wire ch1_data_we;
	wire stg0_vld_out;
	wire ch0_buf_ready;
	wire ch0_pipe_stall;
	wire [1:0] sel_concat;
	wire ch0_buf_data_we;
	wire ch0_buf_vld_rst;
	wire stg0_idle;
	wire stg1_idle;
	wire ch0_is_inactive;
	wire ch1_is_inactive;
	wire [12:0] next_state_val[0:15];
	wire state_we;
	wire ch0_buf_vld_we;
	wire stg1_vld_we;
	wire pipe_idle;

	assign ch1_not_vld = ~ch1_out_buf_vld;
	assign ch0_sel_data = ch0_in_buf_vld ? ch0_in_buf : chan_0_data;
	assign ch0_is_vld = chan_0_vld | ch0_in_buf_vld;
	assign ch1_vld_we = chan_1_rdy | ch1_not_vld;
	assign ch1_data_we = ch0_is_vld & ch1_vld_we;
	assign stg0_vld_out = ch0_is_vld & ch1_data_we;
	assign ch0_buf_ready = ~ch0_in_buf_vld;
	assign ch0_pipe_stall = ~stg0_vld_out;
	assign sel_concat = {ch0_is_vld & ch0_sel_data[0], ch0_is_vld & ~ch0_sel_data[0]};
	assign ch0_buf_data_we = chan_0_vld & ch0_buf_ready & ch0_pipe_stall;
	assign ch0_buf_vld_rst = ch0_in_buf_vld & stg0_vld_out;
	assign stg0_idle = ~ch0_is_vld;
	assign stg1_idle = ~stg1_vld;
	assign ch0_is_inactive = ~(chan_0_vld & ch0_buf_ready);
	assign ch1_is_inactive = ~(ch1_out_buf_vld & chan_1_rdy);

	assign next_state_val[0] = state_array[0] & {13{sel_concat[0]}} | mask_1fff[0] & {13{sel_concat[1]}};
	assign next_state_val[1] = state_array[1] & {13{sel_concat[0]}} | mask_1fff[1] & {13{sel_concat[1]}};
	assign next_state_val[2] = state_array[2] & {13{sel_concat[0]}} | mask_1fff[2] & {13{sel_concat[1]}};
	assign next_state_val[3] = state_array[3] & {13{sel_concat[0]}} | mask_1fff[3] & {13{sel_concat[1]}};
	assign next_state_val[4] = state_array[4] & {13{sel_concat[0]}} | mask_1fff[4] & {13{sel_concat[1]}};
	assign next_state_val[5] = state_array[5] & {13{sel_concat[0]}} | mask_1fff[5] & {13{sel_concat[1]}};
	assign next_state_val[6] = state_array[6] & {13{sel_concat[0]}} | mask_1fff[6] & {13{sel_concat[1]}};
	assign next_state_val[7] = state_array[7] & {13{sel_concat[0]}} | mask_1fff[7] & {13{sel_concat[1]}};
	assign next_state_val[8] = state_array[8] & {13{sel_concat[0]}} | mask_1fff[8] & {13{sel_concat[1]}};
	assign next_state_val[9] = state_array[9] & {13{sel_concat[0]}} | mask_1fff[9] & {13{sel_concat[1]}};
	assign next_state_val[10] = state_array[10] & {13{sel_concat[0]}} | mask_1fff[10] & {13{sel_concat[1]}};
	assign next_state_val[11] = state_array[11] & {13{sel_concat[0]}} | mask_1fff[11] & {13{sel_concat[1]}};
	assign next_state_val[12] = state_array[12] & {13{sel_concat[0]}} | mask_1fff[12] & {13{sel_concat[1]}};
	assign next_state_val[13] = state_array[13] & {13{sel_concat[0]}} | mask_1fff[13] & {13{sel_concat[1]}};
	assign next_state_val[14] = state_array[14] & {13{sel_concat[0]}} | mask_1fff[14] & {13{sel_concat[1]}};
	assign next_state_val[15] = state_array[15] & {13{sel_concat[0]}} | mask_1fff[15] & {13{sel_concat[1]}};

	assign state_we = stg0_vld_out & ch0_sel_data[0] | stg0_vld_out & ~ch0_sel_data[0];
	assign ch0_buf_vld_we = ch0_buf_data_we | ch0_buf_vld_rst;
	assign stg1_vld_we = stg0_vld_out | stg1_vld;
	assign pipe_idle = stg0_idle & stg1_idle & ch0_is_inactive & ch1_is_inactive;

	always @(posedge clk) begin
		if (!rst_n) begin
			state_array[0] <= state_init[0];
			state_array[1] <= state_init[1];
			state_array[2] <= state_init[2];
			state_array[3] <= state_init[3];
			state_array[4] <= state_init[4];
			state_array[5] <= state_init[5];
			state_array[6] <= state_init[6];
			state_array[7] <= state_init[7];
			state_array[8] <= state_init[8];
			state_array[9] <= state_init[9];
			state_array[10] <= state_init[10];
			state_array[11] <= state_init[11];
			state_array[12] <= state_init[12];
			state_array[13] <= state_init[13];
			state_array[14] <= state_init[14];
			state_array[15] <= state_init[15];
			ch0_in_buf <= 4'h0;
			ch0_in_buf_vld <= 1'h0;
			ch1_out_buf[0] <= ch1_init[0];
			ch1_out_buf[1] <= ch1_init[1];
			ch1_out_buf[2] <= ch1_init[2];
			ch1_out_buf[3] <= ch1_init[3];
			ch1_out_buf[4] <= ch1_init[4];
			ch1_out_buf[5] <= ch1_init[5];
			ch1_out_buf[6] <= ch1_init[6];
			ch1_out_buf[7] <= ch1_init[7];
			ch1_out_buf[8] <= ch1_init[8];
			ch1_out_buf[9] <= ch1_init[9];
			ch1_out_buf[10] <= ch1_init[10];
			ch1_out_buf[11] <= ch1_init[11];
			ch1_out_buf[12] <= ch1_init[12];
			ch1_out_buf[13] <= ch1_init[13];
			ch1_out_buf[14] <= ch1_init[14];
			ch1_out_buf[15] <= ch1_init[15];
			ch1_out_buf_vld <= 1'h0;
			stg1_vld <= 1'h0;
		end else begin
			state_array[0] <= state_we ? next_state_val[0] : state_array[0];
			state_array[1] <= state_we ? next_state_val[1] : state_array[1];
			state_array[2] <= state_we ? next_state_val[2] : state_array[2];
			state_array[3] <= state_we ? next_state_val[3] : state_array[3];
			state_array[4] <= state_we ? next_state_val[4] : state_array[4];
			state_array[5] <= state_we ? next_state_val[5] : state_array[5];
			state_array[6] <= state_we ? next_state_val[6] : state_array[6];
			state_array[7] <= state_we ? next_state_val[7] : state_array[7];
			state_array[8] <= state_we ? next_state_val[8] : state_array[8];
			state_array[9] <= state_we ? next_state_val[9] : state_array[9];
			state_array[10] <= state_we ? next_state_val[10] : state_array[10];
			state_array[11] <= state_we ? next_state_val[11] : state_array[11];
			state_array[12] <= state_we ? next_state_val[12] : state_array[12];
			state_array[13] <= state_we ? next_state_val[13] : state_array[13];
			state_array[14] <= state_we ? next_state_val[14] : state_array[14];
			state_array[15] <= state_we ? next_state_val[15] : state_array[15];
			ch0_in_buf <= ch0_buf_data_we ? chan_0_data : ch0_in_buf;
			ch0_in_buf_vld <= ch0_buf_vld_we ? ch0_buf_ready : ch0_in_buf_vld;
			ch1_out_buf[0] <= ch1_data_we ? state_array[0] : ch1_out_buf[0];
			ch1_out_buf[1] <= ch1_data_we ? state_array[1] : ch1_out_buf[1];
			ch1_out_buf[2] <= ch1_data_we ? state_array[2] : ch1_out_buf[2];
			ch1_out_buf[3] <= ch1_data_we ? state_array[3] : ch1_out_buf[3];
			ch1_out_buf[4] <= ch1_data_we ? state_array[4] : ch1_out_buf[4];
			ch1_out_buf[5] <= ch1_data_we ? state_array[5] : ch1_out_buf[5];
			ch1_out_buf[6] <= ch1_data_we ? state_array[6] : ch1_out_buf[6];
			ch1_out_buf[7] <= ch1_data_we ? state_array[7] : ch1_out_buf[7];
			ch1_out_buf[8] <= ch1_data_we ? state_array[8] : ch1_out_buf[8];
			ch1_out_buf[9] <= ch1_data_we ? state_array[9] : ch1_out_buf[9];
			ch1_out_buf[10] <= ch1_data_we ? state_array[10] : ch1_out_buf[10];
			ch1_out_buf[11] <= ch1_data_we ? state_array[11] : ch1_out_buf[11];
			ch1_out_buf[12] <= ch1_data_we ? state_array[12] : ch1_out_buf[12];
			ch1_out_buf[13] <= ch1_data_we ? state_array[13] : ch1_out_buf[13];
			ch1_out_buf[14] <= ch1_data_we ? state_array[14] : ch1_out_buf[14];
			ch1_out_buf[15] <= ch1_data_we ? state_array[15] : ch1_out_buf[15];
			ch1_out_buf_vld <= ch1_vld_we ? ch0_is_vld : ch1_out_buf_vld;
			stg1_vld <= stg1_vld_we ? stg0_vld_out : stg1_vld;
		end
	end

	assign chan_0_rdy = ch0_buf_ready;
	assign chan_1_data = {
		ch1_out_buf[15],
		ch1_out_buf[14],
		ch1_out_buf[13],
		ch1_out_buf[12],
		ch1_out_buf[11],
		ch1_out_buf[10],
		ch1_out_buf[9],
		ch1_out_buf[8],
		ch1_out_buf[7],
		ch1_out_buf[6],
		ch1_out_buf[5],
		ch1_out_buf[4],
		ch1_out_buf[3],
		ch1_out_buf[2],
		ch1_out_buf[1],
		ch1_out_buf[0]
	};
	assign chan_1_vld = ch1_out_buf_vld;
	assign idle = pipe_idle;
endmodule
