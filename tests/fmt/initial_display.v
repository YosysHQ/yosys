module m;
	initial $display("<<<BEGIN>>>");

	initial $display("==> small unsigned %%d");
	initial $display(":%d:",      16'haa);
	initial $display(":%-d:",     16'haa);
	initial $display(":%+d:",     16'haa);
	initial $display(":%+-d:",    16'haa);
	initial $display(":%0d:",     16'haa);
	initial $display(":%-0d:",    16'haa);
	initial $display(":%+0d:",    16'haa);
	initial $display(":%+-0d:",   16'haa);
	initial $display(":%20d:",    16'haa);
	initial $display(":%-20d:",   16'haa);
	initial $display(":%+20d:",   16'haa);
	initial $display(":%+-20d:",  16'haa);
	initial $display(":%020d:",   16'haa);
	initial $display(":%-020d:",  16'haa);
	initial $display(":%+020d:",  16'haa);
	initial $display(":%+-020d:", 16'haa);

	initial $display("==> big unsigned %%d");
	initial $display(":%d:",      16'haaaa);
	initial $display(":%-d:",     16'haaaa);
	initial $display(":%+d:",     16'haaaa);
	initial $display(":%+-d:",    16'haaaa);
	initial $display(":%0d:",     16'haaaa);
	initial $display(":%-0d:",    16'haaaa);
	initial $display(":%+0d:",    16'haaaa);
	initial $display(":%+-0d:",   16'haaaa);
	initial $display(":%20d:",    16'haaaa);
	initial $display(":%-20d:",   16'haaaa);
	initial $display(":%+20d:",   16'haaaa);
	initial $display(":%+-20d:",  16'haaaa);
	initial $display(":%020d:",   16'haaaa);
	initial $display(":%-020d:",  16'haaaa);
	initial $display(":%+020d:",  16'haaaa);
	initial $display(":%+-020d:", 16'haaaa);

	initial $display("==> small signed %%d");
	initial $display(":%d:",      16'shaa);
	initial $display(":%-d:",     16'shaa);
	initial $display(":%+d:",     16'shaa);
	initial $display(":%+-d:",    16'shaa);
	initial $display(":%0d:",     16'shaa);
	initial $display(":%-0d:",    16'shaa);
	initial $display(":%+0d:",    16'shaa);
	initial $display(":%+-0d:",   16'shaa);
	initial $display(":%20d:",    16'shaa);
	initial $display(":%-20d:",   16'shaa);
	initial $display(":%+20d:",   16'shaa);
	initial $display(":%+-20d:",  16'shaa);
	initial $display(":%020d:",   16'shaa);
	initial $display(":%-020d:",  16'shaa);
	initial $display(":%+020d:",  16'shaa);
	initial $display(":%+-020d:", 16'shaa);

	initial $display("==> big signed %%d");
	initial $display(":%d:",      16'shaaaa);
	initial $display(":%-d:",     16'shaaaa);
	initial $display(":%+d:",     16'shaaaa);
	initial $display(":%+-d:",    16'shaaaa);
	initial $display(":%0d:",     16'shaaaa);
	initial $display(":%-0d:",    16'shaaaa);
	initial $display(":%+0d:",    16'shaaaa);
	initial $display(":%+-0d:",   16'shaaaa);
	initial $display(":%20d:",    16'shaaaa);
	initial $display(":%-20d:",   16'shaaaa);
	initial $display(":%+20d:",   16'shaaaa);
	initial $display(":%+-20d:",  16'shaaaa);
	initial $display(":%020d:",   16'shaaaa);
	initial $display(":%-020d:",  16'shaaaa);
	initial $display(":%+020d:",  16'shaaaa);
	initial $display(":%+-020d:", 16'shaaaa);

	initial $display("==> small unsigned %%h");
	initial $display(":%h:",      16'haa);
	initial $display(":%-h:",     16'haa);
	initial $display(":%0h:",     16'haa);
	initial $display(":%-0h:",    16'haa);
	initial $display(":%20h:",    16'haa);
	initial $display(":%-20h:",   16'haa);
	initial $display(":%020h:",   16'haa);
	initial $display(":%-020h:",  16'haa);

	initial $display("==> big unsigned %%h");
	initial $display(":%h:",      16'haaaa);
	initial $display(":%-h:",     16'haaaa);
	initial $display(":%0h:",     16'haaaa);
	initial $display(":%-0h:",    16'haaaa);
	initial $display(":%20h:",    16'haaaa);
	initial $display(":%-20h:",   16'haaaa);
	initial $display(":%020h:",   16'haaaa);
	initial $display(":%-020h:",  16'haaaa);

	initial $display("==> small signed %%h");
	initial $display(":%h:",      16'shaa);
	initial $display(":%-h:",     16'shaa);
	initial $display(":%0h:",     16'shaa);
	initial $display(":%-0h:",    16'shaa);
	initial $display(":%20h:",    16'shaa);
	initial $display(":%-20h:",   16'shaa);
	initial $display(":%020h:",   16'shaa);
	initial $display(":%-020h:",  16'shaa);

	initial $display("==> big signed %%h");
	initial $display(":%h:",      16'shaaaa);
	initial $display(":%-h:",     16'shaaaa);
	initial $display(":%0h:",     16'shaaaa);
	initial $display(":%-0h:",    16'shaaaa);
	initial $display(":%20h:",    16'shaaaa);
	initial $display(":%-20h:",   16'shaaaa);
	initial $display(":%020h:",   16'shaaaa);
	initial $display(":%-020h:",  16'shaaaa);

	initial $display("==> small unsigned %%o");
	initial $display(":%o:",      16'haa);
	initial $display(":%-o:",     16'haa);
	initial $display(":%0o:",     16'haa);
	initial $display(":%-0o:",    16'haa);
	initial $display(":%20o:",    16'haa);
	initial $display(":%-20o:",   16'haa);
	initial $display(":%020o:",   16'haa);
	initial $display(":%-020o:",  16'haa);

	initial $display("==> big unsigned %%o");
	initial $display(":%o:",      16'haaaa);
	initial $display(":%-o:",     16'haaaa);
	initial $display(":%0o:",     16'haaaa);
	initial $display(":%-0o:",    16'haaaa);
	initial $display(":%20o:",    16'haaaa);
	initial $display(":%-20o:",   16'haaaa);
	initial $display(":%020o:",   16'haaaa);
	initial $display(":%-020o:",  16'haaaa);

	initial $display("==> small signed %%o");
	initial $display(":%o:",      16'shaa);
	initial $display(":%-o:",     16'shaa);
	initial $display(":%0o:",     16'shaa);
	initial $display(":%-0o:",    16'shaa);
	initial $display(":%20o:",    16'shaa);
	initial $display(":%-20o:",   16'shaa);
	initial $display(":%020o:",   16'shaa);
	initial $display(":%-020o:",  16'shaa);

	initial $display("==> big signed %%o");
	initial $display(":%o:",      16'shaaaa);
	initial $display(":%-o:",     16'shaaaa);
	initial $display(":%0o:",     16'shaaaa);
	initial $display(":%-0o:",    16'shaaaa);
	initial $display(":%20o:",    16'shaaaa);
	initial $display(":%-20o:",   16'shaaaa);
	initial $display(":%020o:",   16'shaaaa);
	initial $display(":%-020o:",  16'shaaaa);

	initial $display("==> small unsigned %%b");
	initial $display(":%b:",      16'haa);
	initial $display(":%-b:",     16'haa);
	initial $display(":%0b:",     16'haa);
	initial $display(":%-0b:",    16'haa);
	initial $display(":%20b:",    16'haa);
	initial $display(":%-20b:",   16'haa);
	initial $display(":%020b:",   16'haa);
	initial $display(":%-020b:",  16'haa);

	initial $display("==> big unsigned %%b");
	initial $display(":%b:",      16'haaaa);
	initial $display(":%-b:",     16'haaaa);
	initial $display(":%0b:",     16'haaaa);
	initial $display(":%-0b:",    16'haaaa);
	initial $display(":%20b:",    16'haaaa);
	initial $display(":%-20b:",   16'haaaa);
	initial $display(":%020b:",   16'haaaa);
	initial $display(":%-020b:",  16'haaaa);

	initial $display("==> small signed %%b");
	initial $display(":%b:",      16'shaa);
	initial $display(":%-b:",     16'shaa);
	initial $display(":%0b:",     16'shaa);
	initial $display(":%-0b:",    16'shaa);
	initial $display(":%20b:",    16'shaa);
	initial $display(":%-20b:",   16'shaa);
	initial $display(":%020b:",   16'shaa);
	initial $display(":%-020b:",  16'shaa);

	initial $display("==> big signed %%b");
	initial $display(":%b:",      16'shaaaa);
	initial $display(":%-b:",     16'shaaaa);
	initial $display(":%0b:",     16'shaaaa);
	initial $display(":%-0b:",    16'shaaaa);
	initial $display(":%20b:",    16'shaaaa);
	initial $display(":%-20b:",   16'shaaaa);
	initial $display(":%020b:",   16'shaaaa);
	initial $display(":%-020b:",  16'shaaaa);

	initial $display("==> time %%t");
	initial $display(":%t:",      $time);
	initial $display(":%-t:",     $time);
	initial $display(":%0t:",     $time);
	initial $display(":%-0t:",    $time);
	initial $display(":%10t:",    $time);
	initial $display(":%-10t:",   $time);
	initial $display(":%015t:",   $time);
	initial $display(":%-015t:",  $time);

	initial $display("===> %%s");
	initial $display(":%10s:", "foo");
	initial $display(":%010s:", "foo");
	initial $display(":%-10s:", "foo");
	initial $display(":%-010s:", "foo");

	initial $display("===> %%c");
	initial $display(":%10c:", "foo");
	initial $display(":%010c:", "foo");
	initial $display(":%-10c:", "foo");
	initial $display(":%-010c:", "foo");

	initial $display("==> aliases");
	initial $display(":%x:",      16'shaa);
	initial $display(":%X:",      16'shaa);
	initial $display(":%H:",      16'shaa);
	initial $display(":%O:",      16'shaa);
	initial $display(":%B:",      16'shaa);

	initial $display("==> x/z");
	initial $display(":%d:", 16'b1010101010101010);
	initial $display(":%d:", 16'b101010101010101x);
	initial $display(":%d:", 16'b101010101010101z);
	initial $display(":%x:", 16'b1010101010101010);
	initial $display(":%x:", 16'b101010101010101x);
	initial $display(":%x:", 16'b101010101010101z);
	initial $display(":%x:", 16'b101010101010xxxx);
	initial $display(":%x:", 16'b101010101010zzzz);
	initial $display(":%o:", 16'b1010101010101010);
	initial $display(":%o:", 16'b101010101010101x);
	initial $display(":%o:", 16'b101010101010101z);
	initial $display(":%o:", 16'b1010101010101xxx);
	initial $display(":%o:", 16'b1010101010101zzz);
	initial $display(":%b:", 16'b1010101010101010);
	initial $display(":%b:", 16'b101010101010101x);
	initial $display(":%b:", 16'b101010101010101z);

	initial $display("==> default base");
	initial $displayh(16'haa);
	initial $displayo(16'haa);
	initial $displayb(16'haa);

	initial $display("==> write/format");
	initial $display("%d", 1, "%d", 1);
	// this one hits a bug in iverilog:
	// initial $display("%s", $sformatf("%d", 1, "%d", 1));

	initial $display("<<<END>>>");

endmodule
