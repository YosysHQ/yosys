module testbench;
    reg clk;

    initial begin
       //  $dumpfile("testbench.vcd");
       //  $dumpvars(0, testbench);

        #5 clk = 0;
        repeat (10000) begin
            #5 clk = 1;
            #5 clk = 0;
        end
    end


    reg [7:0] data_a = 0;
	reg [7:0] addr_a = 0;
	reg [7:0] addr_b = 0;
    reg we_a = 0;
    reg re_a = 1;
	wire [7:0] q_a;
	reg mem_init = 0;

	reg [7:0] pq_a;

    always @(posedge clk) begin
    #3;
    data_a <= data_a + 17;

    addr_a <= addr_a + 1;
    addr_b <= addr_b + 1;
    end

    always @(posedge addr_a) begin
    #10;
        if(addr_a > 6'h3E)
            mem_init <= 1;
    end

	always @(posedge clk) begin
    //#3;
    we_a <= !we_a;
    end

    reg [7:0] mem [(1<<8)-1:0];

    always @(posedge clk) // Write memory.
	begin
	if (we_a)
	mem[addr_a] <= data_a; // Using write address bus.
	end
	always @(posedge clk) // Read memory.
	begin
	pq_a <= mem[addr_b]; // Using read address bus.
	end

	top uut (
		.din(data_a),
		.write_en(we_a),
		.waddr(addr_a),
		.wclk(clk),
		.raddr(addr_b),
		.rclk(clk),
		.dout(q_a)
		);

	uut_mem_checker port_a_test(.clk(clk), .init(mem_init), .en(!we_a), .A(q_a), .B(pq_a));

endmodule

module uut_mem_checker(input clk, input init, input en, input [7:0] A, input [7:0] B);
    always @(posedge clk)
    begin
        #1;
        if (en == 1 & init == 1 & A !== B)
        begin
            $display("ERROR: ASSERTION FAILED in %m:",$time," ",A," ",B);
            $stop;
        end
    end
endmodule
