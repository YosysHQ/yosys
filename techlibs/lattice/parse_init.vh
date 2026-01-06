function [15:0] parse_init;
	input [((2+(16/4))*8)-1:0] init;
	reg [7:0] c;
	integer i;
	begin
		for (i = 0; i < (16/4); i = i + 1) begin
			c = init[(i * 8) +: 8];
			if (c >= "0" && c <= "9")
				parse_init[(i * 4) +: 4] = (c - "0");
			else if (c >= "A" && c <= "F")
				parse_init[(i * 4) +: 4] = (c - "A") + 10;
			else if (c >= "a" && c <= "f")
				parse_init[(i * 4) +: 4] = (c - "a") + 10;
		end
	end
endfunction

function [63:0] parse_init_64;
	input [((2+(64/4))*8)-1:0] init;
	reg [7:0] c;
	integer i;
	begin
		for (i = 0; i < (64/4); i = i + 1) begin
			c = init[(i * 8) +: 8];
			if (c >= "0" && c <= "9")
				parse_init_64[(i * 4) +: 4] = (c - "0");
			else if (c >= "A" && c <= "F")
				parse_init_64[(i * 4) +: 4] = (c - "A") + 10;
			else if (c >= "a" && c <= "f")
				parse_init_64[(i * 4) +: 4] = (c - "a") + 10;
		end
	end
endfunction
