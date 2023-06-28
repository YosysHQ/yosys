module always_full(input clk, output reg fin);

	reg [7:0] counter = 0;

	always @(posedge clk) begin

		counter <= counter + 1;

		if (counter == 0) fin <= 0;

		if (counter == 1) $display("<<<BEGIN>>>");

		if (counter == 2) $display("==> small unsigned %%d");
		if (counter == 3) $display(":%d:",      16'haa);
		if (counter == 4) $display(":%-d:",     16'haa);
		if (counter == 5) $display(":%+d:",     16'haa);
		if (counter == 6) $display(":%+-d:",    16'haa);
		if (counter == 7) $display(":%0d:",     16'haa);
		if (counter == 8) $display(":%-0d:",    16'haa);
		if (counter == 9) $display(":%+0d:",    16'haa);
		if (counter == 10) $display(":%+-0d:",   16'haa);
		if (counter == 11) $display(":%20d:",    16'haa);
		if (counter == 12) $display(":%-20d:",   16'haa);
		if (counter == 13) $display(":%+20d:",   16'haa);
		if (counter == 14) $display(":%+-20d:",  16'haa);
		if (counter == 15) $display(":%020d:",   16'haa);
		if (counter == 16) $display(":%-020d:",  16'haa);
		if (counter == 17) $display(":%+020d:",  16'haa);
		if (counter == 18) $display(":%+-020d:", 16'haa);

		if (counter == 19) $display("==> big unsigned %%d");
		if (counter == 20) $display(":%d:",      16'haaaa);
		if (counter == 21) $display(":%-d:",     16'haaaa);
		if (counter == 22) $display(":%+d:",     16'haaaa);
		if (counter == 23) $display(":%+-d:",    16'haaaa);
		if (counter == 24) $display(":%0d:",     16'haaaa);
		if (counter == 25) $display(":%-0d:",    16'haaaa);
		if (counter == 26) $display(":%+0d:",    16'haaaa);
		if (counter == 27) $display(":%+-0d:",   16'haaaa);
		if (counter == 28) $display(":%20d:",    16'haaaa);
		if (counter == 29) $display(":%-20d:",   16'haaaa);
		if (counter == 30) $display(":%+20d:",   16'haaaa);
		if (counter == 31) $display(":%+-20d:",  16'haaaa);
		if (counter == 32) $display(":%020d:",   16'haaaa);
		if (counter == 33) $display(":%-020d:",  16'haaaa);
		if (counter == 34) $display(":%+020d:",  16'haaaa);
		if (counter == 35) $display(":%+-020d:", 16'haaaa);

		if (counter == 36) $display("==> small signed %%d");
		if (counter == 37) $display(":%d:",      16'shaa);
		if (counter == 38) $display(":%-d:",     16'shaa);
		if (counter == 39) $display(":%+d:",     16'shaa);
		if (counter == 40) $display(":%+-d:",    16'shaa);
		if (counter == 41) $display(":%0d:",     16'shaa);
		if (counter == 42) $display(":%-0d:",    16'shaa);
		if (counter == 43) $display(":%+0d:",    16'shaa);
		if (counter == 44) $display(":%+-0d:",   16'shaa);
		if (counter == 45) $display(":%20d:",    16'shaa);
		if (counter == 46) $display(":%-20d:",   16'shaa);
		if (counter == 47) $display(":%+20d:",   16'shaa);
		if (counter == 48) $display(":%+-20d:",  16'shaa);
		if (counter == 49) $display(":%020d:",   16'shaa);
		if (counter == 50) $display(":%-020d:",  16'shaa);
		if (counter == 51) $display(":%+020d:",  16'shaa);
		if (counter == 52) $display(":%+-020d:", 16'shaa);

		if (counter == 53) $display("==> big signed %%d");
		if (counter == 54) $display(":%d:",      16'shaaaa);
		if (counter == 55) $display(":%-d:",     16'shaaaa);
		if (counter == 56) $display(":%+d:",     16'shaaaa);
		if (counter == 57) $display(":%+-d:",    16'shaaaa);
		if (counter == 58) $display(":%0d:",     16'shaaaa);
		if (counter == 59) $display(":%-0d:",    16'shaaaa);
		if (counter == 60) $display(":%+0d:",    16'shaaaa);
		if (counter == 61) $display(":%+-0d:",   16'shaaaa);
		if (counter == 62) $display(":%20d:",    16'shaaaa);
		if (counter == 63) $display(":%-20d:",   16'shaaaa);
		if (counter == 64) $display(":%+20d:",   16'shaaaa);
		if (counter == 65) $display(":%+-20d:",  16'shaaaa);
		if (counter == 66) $display(":%020d:",   16'shaaaa);
		if (counter == 67) $display(":%-020d:",  16'shaaaa);
		if (counter == 68) $display(":%+020d:",  16'shaaaa);
		if (counter == 69) $display(":%+-020d:", 16'shaaaa);

		if (counter == 70) $display("==> small unsigned %%h");
		if (counter == 71) $display(":%h:",      16'haa);
		if (counter == 72) $display(":%-h:",     16'haa);
		if (counter == 73) $display(":%0h:",     16'haa);
		if (counter == 74) $display(":%-0h:",    16'haa);
		if (counter == 75) $display(":%20h:",    16'haa);
		if (counter == 76) $display(":%-20h:",   16'haa);
		if (counter == 77) $display(":%020h:",   16'haa);
		if (counter == 78) $display(":%-020h:",  16'haa);

		if (counter == 79) $display("==> big unsigned %%h");
		if (counter == 80) $display(":%h:",      16'haaaa);
		if (counter == 81) $display(":%-h:",     16'haaaa);
		if (counter == 82) $display(":%0h:",     16'haaaa);
		if (counter == 83) $display(":%-0h:",    16'haaaa);
		if (counter == 84) $display(":%20h:",    16'haaaa);
		if (counter == 85) $display(":%-20h:",   16'haaaa);
		if (counter == 86) $display(":%020h:",   16'haaaa);
		if (counter == 87) $display(":%-020h:",  16'haaaa);

		if (counter == 88) $display("==> small signed %%h");
		if (counter == 89) $display(":%h:",      16'shaa);
		if (counter == 90) $display(":%-h:",     16'shaa);
		if (counter == 91) $display(":%0h:",     16'shaa);
		if (counter == 92) $display(":%-0h:",    16'shaa);
		if (counter == 93) $display(":%20h:",    16'shaa);
		if (counter == 94) $display(":%-20h:",   16'shaa);
		if (counter == 95) $display(":%020h:",   16'shaa);
		if (counter == 96) $display(":%-020h:",  16'shaa);

		if (counter == 97) $display("==> big signed %%h");
		if (counter == 98) $display(":%h:",      16'shaaaa);
		if (counter == 99) $display(":%-h:",     16'shaaaa);
		if (counter == 100) $display(":%0h:",     16'shaaaa);
		if (counter == 101) $display(":%-0h:",    16'shaaaa);
		if (counter == 102) $display(":%20h:",    16'shaaaa);
		if (counter == 103) $display(":%-20h:",   16'shaaaa);
		if (counter == 104) $display(":%020h:",   16'shaaaa);
		if (counter == 105) $display(":%-020h:",  16'shaaaa);

		if (counter == 106) $display("==> small unsigned %%o");
		if (counter == 107) $display(":%o:",      16'haa);
		if (counter == 108) $display(":%-o:",     16'haa);
		if (counter == 109) $display(":%0o:",     16'haa);
		if (counter == 110) $display(":%-0o:",    16'haa);
		if (counter == 111) $display(":%20o:",    16'haa);
		if (counter == 112) $display(":%-20o:",   16'haa);
		if (counter == 113) $display(":%020o:",   16'haa);
		if (counter == 114) $display(":%-020o:",  16'haa);

		if (counter == 115) $display("==> big unsigned %%o");
		if (counter == 116) $display(":%o:",      16'haaaa);
		if (counter == 117) $display(":%-o:",     16'haaaa);
		if (counter == 118) $display(":%0o:",     16'haaaa);
		if (counter == 119) $display(":%-0o:",    16'haaaa);
		if (counter == 120) $display(":%20o:",    16'haaaa);
		if (counter == 121) $display(":%-20o:",   16'haaaa);
		if (counter == 122) $display(":%020o:",   16'haaaa);
		if (counter == 123) $display(":%-020o:",  16'haaaa);

		if (counter == 124) $display("==> small signed %%o");
		if (counter == 125) $display(":%o:",      16'shaa);
		if (counter == 126) $display(":%-o:",     16'shaa);
		if (counter == 127) $display(":%0o:",     16'shaa);
		if (counter == 128) $display(":%-0o:",    16'shaa);
		if (counter == 129) $display(":%20o:",    16'shaa);
		if (counter == 130) $display(":%-20o:",   16'shaa);
		if (counter == 131) $display(":%020o:",   16'shaa);
		if (counter == 132) $display(":%-020o:",  16'shaa);

		if (counter == 133) $display("==> big signed %%o");
		if (counter == 134) $display(":%o:",      16'shaaaa);
		if (counter == 135) $display(":%-o:",     16'shaaaa);
		if (counter == 136) $display(":%0o:",     16'shaaaa);
		if (counter == 137) $display(":%-0o:",    16'shaaaa);
		if (counter == 138) $display(":%20o:",    16'shaaaa);
		if (counter == 139) $display(":%-20o:",   16'shaaaa);
		if (counter == 140) $display(":%020o:",   16'shaaaa);
		if (counter == 141) $display(":%-020o:",  16'shaaaa);

		if (counter == 142) $display("==> small unsigned %%b");
		if (counter == 143) $display(":%b:",      16'haa);
		if (counter == 144) $display(":%-b:",     16'haa);
		if (counter == 145) $display(":%0b:",     16'haa);
		if (counter == 146) $display(":%-0b:",    16'haa);
		if (counter == 147) $display(":%20b:",    16'haa);
		if (counter == 148) $display(":%-20b:",   16'haa);
		if (counter == 149) $display(":%020b:",   16'haa);
		if (counter == 150) $display(":%-020b:",  16'haa);

		if (counter == 151) $display("==> big unsigned %%b");
		if (counter == 152) $display(":%b:",      16'haaaa);
		if (counter == 153) $display(":%-b:",     16'haaaa);
		if (counter == 154) $display(":%0b:",     16'haaaa);
		if (counter == 155) $display(":%-0b:",    16'haaaa);
		if (counter == 156) $display(":%20b:",    16'haaaa);
		if (counter == 157) $display(":%-20b:",   16'haaaa);
		if (counter == 158) $display(":%020b:",   16'haaaa);
		if (counter == 159) $display(":%-020b:",  16'haaaa);

		if (counter == 160) $display("==> small signed %%b");
		if (counter == 161) $display(":%b:",      16'shaa);
		if (counter == 162) $display(":%-b:",     16'shaa);
		if (counter == 163) $display(":%0b:",     16'shaa);
		if (counter == 164) $display(":%-0b:",    16'shaa);
		if (counter == 165) $display(":%20b:",    16'shaa);
		if (counter == 166) $display(":%-20b:",   16'shaa);
		if (counter == 167) $display(":%020b:",   16'shaa);
		if (counter == 168) $display(":%-020b:",  16'shaa);

		if (counter == 169) $display("==> big signed %%b");
		if (counter == 170) $display(":%b:",      16'shaaaa);
		if (counter == 171) $display(":%-b:",     16'shaaaa);
		if (counter == 172) $display(":%0b:",     16'shaaaa);
		if (counter == 173) $display(":%-0b:",    16'shaaaa);
		if (counter == 174) $display(":%20b:",    16'shaaaa);
		if (counter == 175) $display(":%-20b:",   16'shaaaa);
		if (counter == 176) $display(":%020b:",   16'shaaaa);
		if (counter == 177) $display(":%-020b:",  16'shaaaa);

		if (counter == 178) $display("==> time %%t");
		if (counter == 179) $display(":%t:",      $time);
		if (counter == 180) $display(":%-t:",     $time);
		if (counter == 181) $display(":%0t:",     $time);
		if (counter == 182) $display(":%-0t:",    $time);
		if (counter == 183) $display(":%10t:",    $time);
		if (counter == 184) $display(":%-10t:",   $time);
		if (counter == 185) $display(":%015t:",   $time);
		if (counter == 186) $display(":%-015t:",  $time);

		if (counter == 187) $display("===> %%s");
		if (counter == 188) $display(":%10s:", "foo");
		if (counter == 189) $display(":%010s:", "foo");
		if (counter == 190) $display(":%-10s:", "foo");
		if (counter == 191) $display(":%-010s:", "foo");

		if (counter == 192) $display("===> %%c");
		if (counter == 193) $display(":%10c:", "foo");
		if (counter == 194) $display(":%010c:", "foo");
		if (counter == 195) $display(":%-10c:", "foo");
		if (counter == 196) $display(":%-010c:", "foo");

		if (counter == 197) $display("==> aliases");
		if (counter == 198) $display(":%x:",      16'shaa);
		if (counter == 199) $display(":%X:",      16'shaa);
		if (counter == 200) $display(":%H:",      16'shaa);
		if (counter == 201) $display(":%O:",      16'shaa);
		if (counter == 202) $display(":%B:",      16'shaa);

		if (counter == 203) $display("==> default base");
		if (counter == 204) $displayh(16'haa);
		if (counter == 205) $displayo(16'haa);
		if (counter == 206) $displayb(16'haa);

		if (counter == 207) $display("==> write/format");
		if (counter == 208) $display("%d", 1, "%d", 1);

		if (counter == 209) begin
			$display("<<<END>>>");
			fin <= 1;
		end

	end

endmodule
