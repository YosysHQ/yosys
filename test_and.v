`ifndef outfile
	`define outfile "/dev/stdout"
`endif
module testbench;

integer i;
integer file;

reg [1023:0] filename;

reg [31:0] xorshift128_x = 123456789;
reg [31:0] xorshift128_y = 362436069;
reg [31:0] xorshift128_z = 521288629;
reg [31:0] xorshift128_w = 1716918015; // <-- seed value
reg [31:0] xorshift128_t;

task xorshift128;
begin
	xorshift128_t = xorshift128_x ^ (xorshift128_x << 11);
	xorshift128_x = xorshift128_y;
	xorshift128_y = xorshift128_z;
	xorshift128_z = xorshift128_w;
	xorshift128_w = xorshift128_w ^ (xorshift128_w >> 19) ^ xorshift128_t ^ (xorshift128_t >> 8);
end
endtask

wire [0:0] sig_my_module_y;
reg [0:0] sig_my_module_b;
reg [0:0] sig_my_module_a;
my_module uut_my_module(
	.y(sig_my_module_y),
	.b(sig_my_module_b),
	.a(sig_my_module_a)
);

task my_module_reset;
begin
	sig_my_module_a <= #2 0;
	sig_my_module_b <= #4 0;
	#100;
	sig_my_module_a <= #2 ~0;
	sig_my_module_b <= #4 ~0;
	#100;
	#0;
end
endtask

task my_module_update_data;
begin
	xorshift128;
	sig_my_module_a <= #2 { xorshift128_x, xorshift128_y, xorshift128_z, xorshift128_w };
	xorshift128;
	sig_my_module_b <= #4 { xorshift128_x, xorshift128_y, xorshift128_z, xorshift128_w };
	#100;
end
endtask

task my_module_update_clock;
begin
end
endtask

task my_module_print_status;
begin
	$fdisplay(file, "#OUT# %b %b %b %t %d", { sig_my_module_a, sig_my_module_b }, { 1'bx }, { sig_my_module_y }, $time, i);
end
endtask

task my_module_print_header;
begin
	$fdisplay(file, "#OUT#");
	$fdisplay(file, "#OUT#   A   sig_my_module_a");
	$fdisplay(file, "#OUT#   B   sig_my_module_b");
	$fdisplay(file, "#OUT#   C   sig_my_module_y");
	$fdisplay(file, "#OUT#");
	$fdisplay(file, {"#OUT# ", "A", "B", " ", "#", " ", "C"});
end
endtask

task my_module_test;
begin
	$fdisplay(file, "#OUT#\n#OUT# ==== my_module ====");
	my_module_reset;
	for (i=0; i<1000; i=i+1) begin
		if (i % 20 == 0) my_module_print_header;
		#100; my_module_update_data;
		#100; my_module_update_clock;
		#100; my_module_print_status;
	end
end
endtask

initial begin
	if ($value$plusargs("VCD=%s", filename)) begin
		$dumpfile(filename);
		$dumpvars(0, testbench);
	end
	if ($value$plusargs("OUT=%s", filename)) begin
		file = $fopen(filename);
	end else begin
		file = $fopen(`outfile);
	end
	my_module_test;
	$fclose(file);
	$finish;
end

endmodule
