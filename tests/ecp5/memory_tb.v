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
	reg [5:0] addr_a = 0;
    reg we_a = 0;
    reg re_a = 1;
	wire [7:0] q_a;
	reg mem_init = 0;

	reg [7:0] pq_a;

    top uut (
    .data_a(data_a),
	.addr_a(addr_a),
	.we_a(we_a),
	.clk(clk),
	.q_a(q_a)
    );

    always @(posedge clk) begin
    #3;
    data_a <= data_a + 17;

    addr_a <= addr_a + 1;
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

    // Declare the RAM variable for check
	reg [7:0] ram[63:0];

	// Port A for check
	always @ (posedge clk)
	begin
		if (we_a)
		begin
			ram[addr_a] <= data_a;
			pq_a <= data_a;
		end
		pq_a <= ram[addr_a];
	end

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
