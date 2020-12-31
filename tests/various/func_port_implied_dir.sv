module gate(w, x, y, z);
	function automatic integer bar(
		integer a
	);
		bar = 2 ** a;
	endfunction
	output integer w = bar(4);

	function automatic integer foo(
		input integer a, /* implicitly input */ integer b,
		output integer c, /* implicitly output */ integer d
	);
		c = 42;
		d = 51;
		foo = a + b + 1;
	endfunction
	output integer x, y, z;
	initial x = foo(1, 2, y, z);
endmodule

module gold(w, x, y, z);
	output integer w = 16, x = 4, y = 42, z = 51;
endmodule
