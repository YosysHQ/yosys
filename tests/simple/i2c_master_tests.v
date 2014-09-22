// one of my early test cases was the OpenCores I2C master
// This is a collection of stripped down code snippets from
// this core that triggered bugs in early versions of yosys.

// from i2c_master_bit_ctrl
module i2c_test01(clk, rst, nReset, al);

	input clk, rst, nReset;
	output reg al;

	reg cmd_stop;
	always @(posedge clk or negedge nReset)
	  if (~nReset)
	    cmd_stop <= #1 1'b0;
	  else if (rst)
	    cmd_stop <= #1 1'b0;

	always @(posedge clk or negedge nReset)
	  if (~nReset)
	    al <= #1 1'b0;
	  else if (rst)
	    al <= #1 1'b0;
	  else
	    al <= #1 ~cmd_stop;

endmodule

// from i2c_master_bit_ctrl
module i2c_test02(clk, slave_wait, clk_cnt, cmd, cmd_stop, cnt);

	input clk, slave_wait, clk_cnt;
	input cmd;

	output reg cmd_stop;

	reg clk_en;
	output reg [15:0] cnt;

	always @(posedge clk)
	  if (~|cnt)
	    if (~slave_wait)
	      begin
	          cnt    <= #1 clk_cnt;
	          clk_en <= #1 1'b1;
	      end
	    else
	      begin
	          cnt    <= #1 cnt;
	          clk_en <= #1 1'b0;
	      end
	  else
	    begin
                cnt    <= #1 cnt - 16'h1;
	        clk_en <= #1 1'b0;
	    end

	always @(posedge clk)
	  if (clk_en)
	    cmd_stop <= #1 cmd;

endmodule

