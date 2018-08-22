/* A simple Yosys plugin. (Copy&paste from http://stackoverflow.com/questions/32093541/how-does-the-yosys-consteval-api-work)

Usage example:

$ cat > evaldemo.v <<EOT
module main(input [1:0] A, input [7:0] B, C, D, output [7:0] Y);
  assign Y = A == 0 ? B : A == 1 ? C : A == 2 ? D : 42;
endmodule
EOT

$ yosys-config --build evaldemo.so evaldemo.cc
$ yosys -m evaldemo.so -p evaldemo evaldemo.v
*/

#include "kernel/yosys.h"
#include "kernel/consteval.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct EvalDemoPass : public Pass
{
	EvalDemoPass() : Pass("evaldemo") { }

	void execute(vector<string>, Design *design) YS_OVERRIDE
	{
		Module *module = design->top_module();

		if (module == nullptr)
			log_error("No top module found!\n");

		Wire *wire_a = module->wire("\\A");
		Wire *wire_y = module->wire("\\Y");

		if (wire_a == nullptr)
			log_error("No wire A found!\n");

		if (wire_y == nullptr)
			log_error("No wire Y found!\n");

		ConstEval ce(module);
		for (int v = 0; v < 4; v++) {
			ce.push();
			ce.set(wire_a, Const(v, GetSize(wire_a)));
			SigSpec sig_y = wire_y, sig_undef;
			if (ce.eval(sig_y, sig_undef))
				log("Eval results for A=%d: Y=%s\n", v, log_signal(sig_y));
			else
				log("Eval failed for A=%d: Missing value for %s\n", v, log_signal(sig_undef));
			ce.pop();
		}
	}
} EvalDemoPass;

PRIVATE_NAMESPACE_END
