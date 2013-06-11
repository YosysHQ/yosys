
#include <sys/stat.h>
#include <sys/types.h>
#include <stdio.h>
#include <string>

const char *arg_types[][2] = {
	{ "{dir} [3:0] {name}", "{name}" },		// 00
	{ "{dir} [4:0] {name}", "{name}" },		// 01
	{ "{dir} [5:0] {name}", "{name}" },		// 02
	{ "{dir} signed [3:0] {name}", "{name}" },	// 03
	{ "{dir} signed [4:0] {name}", "{name}" },	// 04
	{ "{dir} signed [5:0] {name}", "{name}" }	// 05
};

// See Table 5-1 (page 42) in IEEE Std 1364-2005
// for a list of all Verilog oprators.

const char *binary_ops[] = {
	"+",	// 00
	"-",	// 01
	"*",	// 02
//	"/",
//	"%",
//	"**",
	">",	// 03
	">=",	// 04
	"<",	// 05
	"<=",	// 06
	"&&",	// 07
	"||",	// 08
	"==",	// 09
	"!=",	// 10
	"===",	// 11
	"!==",	// 12
	"&",	// 13
	"|",	// 14
	"^",	// 15
	"^~",	// 16
	"<<",	// 17
	">>",	// 18
	"<<<",	// 19
	">>>",	// 20
};

const char *unary_ops[] = {
	"+",	// 00
	"-",	// 01
	"!",	// 02
	"~",	// 03
	"&",	// 04
	"~&",	// 05
	"|",	// 06
	"~|",	// 07
	"^",	// 08
	"~^",	// 09
};

void strsubst(std::string &str, const std::string &match, const std::string &replace)
{
	size_t pos;
	while ((pos = str.find(match)) != std::string::npos)
		str.replace(pos, match.size(), replace);
}

int main()
{
	mkdir("rtl", 0777);

	// generate test cases for binary operators

	for (int ai = 0; ai < sizeof(arg_types)/sizeof(arg_types[0]); ai++)
	for (int bi = 0; bi < sizeof(arg_types)/sizeof(arg_types[0]); bi++)
	for (int yi = 0; yi < sizeof(arg_types)/sizeof(arg_types[0]); yi++)
	for (int oi = 0; oi < sizeof(binary_ops)/sizeof(binary_ops[0]); oi++)
	{
		std::string a_decl = arg_types[ai][0];
		strsubst(a_decl, "{dir}", "input");
		strsubst(a_decl, "{name}", "a");

		std::string b_decl = arg_types[bi][0];
		strsubst(b_decl, "{dir}", "input");
		strsubst(b_decl, "{name}", "b");

		std::string y_decl = arg_types[yi][0];
		strsubst(y_decl, "{dir}", "output");
		strsubst(y_decl, "{name}", "y");

		std::string a_ref = arg_types[ai][1];
		strsubst(a_ref, "{dir}", "input");
		strsubst(a_ref, "{name}", "a");

		std::string b_ref = arg_types[bi][1];
		strsubst(b_ref, "{dir}", "input");
		strsubst(b_ref, "{name}", "b");

		std::string y_ref = arg_types[yi][1];
		strsubst(y_ref, "{dir}", "output");
		strsubst(y_ref, "{name}", "y");

		char buffer[1024];
		snprintf(buffer, 1024, "rtl/binary_ops_%02d%02d%02d%02d.v", ai, bi, yi, oi);

		FILE *f = fopen(buffer, "w");
		fprintf(f, "module binary_ops_%02d%02d%02d%02d(a, b, y);\n", ai, bi, yi, oi);
		fprintf(f, "%s;\n", a_decl.c_str());
		fprintf(f, "%s;\n", b_decl.c_str());
		fprintf(f, "%s;\n", y_decl.c_str());
		fprintf(f, "assign %s = %s %s %s;\n", y_ref.c_str(),
				a_ref.c_str(), binary_ops[oi], b_ref.c_str());
		fprintf(f, "endmodule\n");
		fclose(f);
	}

	// generate test cases for unary operators

	for (int ai = 0; ai < sizeof(arg_types)/sizeof(arg_types[0]); ai++)
	for (int yi = 0; yi < sizeof(arg_types)/sizeof(arg_types[0]); yi++)
	for (int oi = 0; oi < sizeof(unary_ops)/sizeof(unary_ops[0]); oi++)
	{
		std::string a_decl = arg_types[ai][0];
		strsubst(a_decl, "{dir}", "input");
		strsubst(a_decl, "{name}", "a");

		std::string y_decl = arg_types[yi][0];
		strsubst(y_decl, "{dir}", "output");
		strsubst(y_decl, "{name}", "y");

		std::string a_ref = arg_types[ai][1];
		strsubst(a_ref, "{dir}", "input");
		strsubst(a_ref, "{name}", "a");

		std::string y_ref = arg_types[yi][1];
		strsubst(y_ref, "{dir}", "output");
		strsubst(y_ref, "{name}", "y");

		char buffer[1024];
		snprintf(buffer, 1024, "rtl/unary_ops_%02d%02d%02d.v", ai, yi, oi);

		FILE *f = fopen(buffer, "w");
		fprintf(f, "module unary_ops_%02d%02d%02d(a, b, y);\n", ai, yi, oi);
		fprintf(f, "%s;\n", a_decl.c_str());
		fprintf(f, "%s;\n", y_decl.c_str());
		fprintf(f, "assign %s = %s %s;\n", y_ref.c_str(),
				unary_ops[oi], a_ref.c_str());
		fprintf(f, "endmodule\n");
		fclose(f);
	}

	return 0;
}

