module top;
    reg [0:7] mem [0:2];

    initial mem[1] = '1;
    wire [31:0] a, b, c, d;
    assign a = mem[1];
    assign b = mem[-1];
    assign c = mem[-1][0];
    assign d = mem[-1][0:1];

    always @* begin

    	assert ($countbits(a, '0) == 24);
    	assert ($countbits(a, '1) == 8);
    	assert ($countbits(a, 'x) == 0);

    	assert ($countbits(b, '0) == 24);
    	assert ($countbits(b, 'x) == 8);

    	assert ($countbits(c, '0) == 31);
    	assert ($countbits(c, 'x) == 1);

    	assert ($countbits(d, '0) == 30);
    	assert ($countbits(d, 'x) == 2);

    end
endmodule
