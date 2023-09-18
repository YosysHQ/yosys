module always_full(input clk);

	always @(posedge clk) begin

		$display("==> small unsigned %%d");
		$display(":%d:",      16'haa);
		$display(":%-d:",     16'haa);
		$display(":%+d:",     16'haa);
		$display(":%+-d:",    16'haa);
		$display(":%0d:",     16'haa);
		$display(":%-0d:",    16'haa);
		$display(":%+0d:",    16'haa);
		$display(":%+-0d:",   16'haa);
		$display(":%20d:",    16'haa);
		$display(":%-20d:",   16'haa);
		$display(":%+20d:",   16'haa);
		$display(":%+-20d:",  16'haa);
		$display(":%020d:",   16'haa);
		$display(":%-020d:",  16'haa);
		$display(":%+020d:",  16'haa);
		$display(":%+-020d:", 16'haa);

		$display("==> big unsigned %%d");
		$display(":%d:",      16'haaaa);
		$display(":%-d:",     16'haaaa);
		$display(":%+d:",     16'haaaa);
		$display(":%+-d:",    16'haaaa);
		$display(":%0d:",     16'haaaa);
		$display(":%-0d:",    16'haaaa);
		$display(":%+0d:",    16'haaaa);
		$display(":%+-0d:",   16'haaaa);
		$display(":%20d:",    16'haaaa);
		$display(":%-20d:",   16'haaaa);
		$display(":%+20d:",   16'haaaa);
		$display(":%+-20d:",  16'haaaa);
		$display(":%020d:",   16'haaaa);
		$display(":%-020d:",  16'haaaa);
		$display(":%+020d:",  16'haaaa);
		$display(":%+-020d:", 16'haaaa);

		$display("==> small signed %%d");
		$display(":%d:",      16'shaa);
		$display(":%-d:",     16'shaa);
		$display(":%+d:",     16'shaa);
		$display(":%+-d:",    16'shaa);
		$display(":%0d:",     16'shaa);
		$display(":%-0d:",    16'shaa);
		$display(":%+0d:",    16'shaa);
		$display(":%+-0d:",   16'shaa);
		$display(":%20d:",    16'shaa);
		$display(":%-20d:",   16'shaa);
		$display(":%+20d:",   16'shaa);
		$display(":%+-20d:",  16'shaa);
		$display(":%020d:",   16'shaa);
		$display(":%-020d:",  16'shaa);
		$display(":%+020d:",  16'shaa);
		$display(":%+-020d:", 16'shaa);

		$display("==> big signed %%d");
		$display(":%d:",      16'shaaaa);
		$display(":%-d:",     16'shaaaa);
		$display(":%+d:",     16'shaaaa);
		$display(":%+-d:",    16'shaaaa);
		$display(":%0d:",     16'shaaaa);
		$display(":%-0d:",    16'shaaaa);
		$display(":%+0d:",    16'shaaaa);
		$display(":%+-0d:",   16'shaaaa);
		$display(":%20d:",    16'shaaaa);
		$display(":%-20d:",   16'shaaaa);
		$display(":%+20d:",   16'shaaaa);
		$display(":%+-20d:",  16'shaaaa);
		$display(":%020d:",   16'shaaaa);
		$display(":%-020d:",  16'shaaaa);
		$display(":%+020d:",  16'shaaaa);
		$display(":%+-020d:", 16'shaaaa);

		$display("==> small unsigned %%h");
		$display(":%h:",      16'haa);
		$display(":%-h:",     16'haa);
		$display(":%0h:",     16'haa);
		$display(":%-0h:",    16'haa);
		$display(":%20h:",    16'haa);
		$display(":%-20h:",   16'haa);
		$display(":%020h:",   16'haa);
		$display(":%-020h:",  16'haa);

		$display("==> big unsigned %%h");
		$display(":%h:",      16'haaaa);
		$display(":%-h:",     16'haaaa);
		$display(":%0h:",     16'haaaa);
		$display(":%-0h:",    16'haaaa);
		$display(":%20h:",    16'haaaa);
		$display(":%-20h:",   16'haaaa);
		$display(":%020h:",   16'haaaa);
		$display(":%-020h:",  16'haaaa);

		$display("==> small signed %%h");
		$display(":%h:",      16'shaa);
		$display(":%-h:",     16'shaa);
		$display(":%0h:",     16'shaa);
		$display(":%-0h:",    16'shaa);
		$display(":%20h:",    16'shaa);
		$display(":%-20h:",   16'shaa);
		$display(":%020h:",   16'shaa);
		$display(":%-020h:",  16'shaa);

		$display("==> big signed %%h");
		$display(":%h:",      16'shaaaa);
		$display(":%-h:",     16'shaaaa);
		$display(":%0h:",     16'shaaaa);
		$display(":%-0h:",    16'shaaaa);
		$display(":%20h:",    16'shaaaa);
		$display(":%-20h:",   16'shaaaa);
		$display(":%020h:",   16'shaaaa);
		$display(":%-020h:",  16'shaaaa);

		$display("==> small unsigned %%o");
		$display(":%o:",      16'haa);
		$display(":%-o:",     16'haa);
		$display(":%0o:",     16'haa);
		$display(":%-0o:",    16'haa);
		$display(":%20o:",    16'haa);
		$display(":%-20o:",   16'haa);
		$display(":%020o:",   16'haa);
		$display(":%-020o:",  16'haa);

		$display("==> big unsigned %%o");
		$display(":%o:",      16'haaaa);
		$display(":%-o:",     16'haaaa);
		$display(":%0o:",     16'haaaa);
		$display(":%-0o:",    16'haaaa);
		$display(":%20o:",    16'haaaa);
		$display(":%-20o:",   16'haaaa);
		$display(":%020o:",   16'haaaa);
		$display(":%-020o:",  16'haaaa);

		$display("==> small signed %%o");
		$display(":%o:",      16'shaa);
		$display(":%-o:",     16'shaa);
		$display(":%0o:",     16'shaa);
		$display(":%-0o:",    16'shaa);
		$display(":%20o:",    16'shaa);
		$display(":%-20o:",   16'shaa);
		$display(":%020o:",   16'shaa);
		$display(":%-020o:",  16'shaa);

		$display("==> big signed %%o");
		$display(":%o:",      16'shaaaa);
		$display(":%-o:",     16'shaaaa);
		$display(":%0o:",     16'shaaaa);
		$display(":%-0o:",    16'shaaaa);
		$display(":%20o:",    16'shaaaa);
		$display(":%-20o:",   16'shaaaa);
		$display(":%020o:",   16'shaaaa);
		$display(":%-020o:",  16'shaaaa);

		$display("==> small unsigned %%b");
		$display(":%b:",      16'haa);
		$display(":%-b:",     16'haa);
		$display(":%0b:",     16'haa);
		$display(":%-0b:",    16'haa);
		$display(":%20b:",    16'haa);
		$display(":%-20b:",   16'haa);
		$display(":%020b:",   16'haa);
		$display(":%-020b:",  16'haa);

		$display("==> big unsigned %%b");
		$display(":%b:",      16'haaaa);
		$display(":%-b:",     16'haaaa);
		$display(":%0b:",     16'haaaa);
		$display(":%-0b:",    16'haaaa);
		$display(":%20b:",    16'haaaa);
		$display(":%-20b:",   16'haaaa);
		$display(":%020b:",   16'haaaa);
		$display(":%-020b:",  16'haaaa);

		$display("==> small signed %%b");
		$display(":%b:",      16'shaa);
		$display(":%-b:",     16'shaa);
		$display(":%0b:",     16'shaa);
		$display(":%-0b:",    16'shaa);
		$display(":%20b:",    16'shaa);
		$display(":%-20b:",   16'shaa);
		$display(":%020b:",   16'shaa);
		$display(":%-020b:",  16'shaa);

		$display("==> big signed %%b");
		$display(":%b:",      16'shaaaa);
		$display(":%-b:",     16'shaaaa);
		$display(":%0b:",     16'shaaaa);
		$display(":%-0b:",    16'shaaaa);
		$display(":%20b:",    16'shaaaa);
		$display(":%-20b:",   16'shaaaa);
		$display(":%020b:",   16'shaaaa);
		$display(":%-020b:",  16'shaaaa);

		$display("==> time %%t");
		$display(":%t:",      $time);
		$display(":%-t:",     $time);
		$display(":%0t:",     $time);
		$display(":%-0t:",    $time);
		$display(":%10t:",    $time);
		$display(":%-10t:",   $time);
		$display(":%015t:",   $time);
		$display(":%-015t:",  $time);

		$display("===> %%s");
		$display(":%10s:", "foo");
		$display(":%010s:", "foo");
		$display(":%-10s:", "foo");
		$display(":%-010s:", "foo");

		$display("===> %%c");
		$display(":%10c:", "foo");
		$display(":%010c:", "foo");
		$display(":%-10c:", "foo");
		$display(":%-010c:", "foo");

		$display("==> aliases");
		$display(":%x:",      16'shaa);
		$display(":%X:",      16'shaa);
		$display(":%H:",      16'shaa);
		$display(":%O:",      16'shaa);
		$display(":%B:",      16'shaa);

		$display("==> default base");
		$displayh(16'haa);
		$displayo(16'haa);
		$displayb(16'haa);

		$display("==> write/format");
		$display("%d", 1, "%d", 1);

	end

endmodule
