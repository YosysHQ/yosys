
#define GENERATE_BINARY_OPS
#define GENERATE_UNARY_OPS
#define GENERATE_TERNARY_OPS
#define GENERATE_CONCAT_OPS

#include <sys/stat.h>
#include <sys/types.h>
#include <string.h>
#include <stdio.h>
#include <string>

const char *arg_types[][3] = {
	{ "{dir} [3:0] {name}", "{name}", "4" },	// 00
	{ "{dir} [4:0] {name}", "{name}", "5" },	// 01
	{ "{dir} [5:0] {name}", "{name}", "6" },	// 02
	{ "{dir} signed [3:0] {name}", "{name}", "4" },	// 03
	{ "{dir} signed [4:0] {name}", "{name}", "5" },	// 04
	{ "{dir} signed [5:0] {name}", "{name}", "6" }	// 05
};

const char *small_arg_types[][3] = {
	{ "{dir} [0:0] {name}", "{name}", "1" },	// 00
	{ "{dir} [1:0] {name}", "{name}", "2" },	// 01
	{ "{dir} [2:0] {name}", "{name}", "3" },	// 02
	{ "{dir} signed [0:0] {name}", "{name}", "1" },	// 03
	{ "{dir} signed [1:0] {name}", "{name}", "2" },	// 04
	{ "{dir} signed [2:0] {name}", "{name}", "3" },	// 05
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

#ifdef GENERATE_BINARY_OPS
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
#endif

#ifdef GENERATE_UNARY_OPS
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
		fprintf(f, "input b;\n");
		fprintf(f, "%s;\n", y_decl.c_str());
		fprintf(f, "assign %s = %s %s;\n", y_ref.c_str(),
				unary_ops[oi], a_ref.c_str());
		fprintf(f, "endmodule\n");
		fclose(f);
	}
#endif

#ifdef GENERATE_TERNARY_OPS
	for (int ai = 0; ai < sizeof(small_arg_types)/sizeof(small_arg_types[0]); ai++)
	for (int bi = 0; bi < sizeof(arg_types)/sizeof(arg_types[0]); bi++)
	for (int ci = 0; ci < sizeof(arg_types)/sizeof(arg_types[0]); ci++)
	for (int yi = 0; yi < sizeof(arg_types)/sizeof(arg_types[0]); yi++)
	{
		if (!strcmp(small_arg_types[ai][2], "3"))
			continue;
		if (!strcmp(arg_types[bi][2], "6"))
			continue;
		if (!strcmp(arg_types[ci][2], "6"))
			continue;

		std::string a_decl = small_arg_types[ai][0];
		strsubst(a_decl, "{dir}", "input");
		strsubst(a_decl, "{name}", "a");

		std::string b1_decl = arg_types[bi][0];
		strsubst(b1_decl, "{dir}", "wire");
		strsubst(b1_decl, "{name}", "b1");

		std::string b2_decl = arg_types[ci][0];
		strsubst(b2_decl, "{dir}", "wire");
		strsubst(b2_decl, "{name}", "b2");

		std::string y_decl = arg_types[yi][0];
		strsubst(y_decl, "{dir}", "output");
		strsubst(y_decl, "{name}", "y");

		std::string a_ref = small_arg_types[ai][1];
		strsubst(a_ref, "{dir}", "input");
		strsubst(a_ref, "{name}", "a");

		std::string b1_ref = arg_types[bi][1];
		strsubst(b1_ref, "{dir}", "wire");
		strsubst(b1_ref, "{name}", "b1");

		std::string b2_ref = arg_types[ci][1];
		strsubst(b2_ref, "{dir}", "wire");
		strsubst(b2_ref, "{name}", "b2");

		std::string y_ref = arg_types[yi][1];
		strsubst(y_ref, "{dir}", "output");
		strsubst(y_ref, "{name}", "y");

		char buffer[1024];
		snprintf(buffer, 1024, "rtl/ternary_ops_%02d%02d%02d%02d.v", ai, bi, ci, yi);

		FILE *f = fopen(buffer, "w");
		fprintf(f, "module ternary_ops_%02d%02d%02d%02d(a, b, y);\n", ai, bi, ci, yi);
		fprintf(f, "%s;\n", a_decl.c_str());
		fprintf(f, "input [%s+%s-1:0] b;\n", arg_types[bi][2], arg_types[ci][2]);
		fprintf(f, "%s = b[%s+%s-1:%s];\n", b1_decl.c_str(), arg_types[bi][2], arg_types[ci][2], arg_types[ci][2]);
		fprintf(f, "%s = b[%s-1:0];\n", b2_decl.c_str(), arg_types[ci][2]);
		fprintf(f, "%s;\n", y_decl.c_str());
		fprintf(f, "assign %s = %s ? %s : %s;\n", y_ref.c_str(),
				a_ref.c_str(), b1_ref.c_str(), b2_ref.c_str());
		fprintf(f, "endmodule\n");
		fclose(f);
	}
#endif

#ifdef GENERATE_CONCAT_OPS
	for (int ai = 0; ai < sizeof(small_arg_types)/sizeof(small_arg_types[0]); ai++)
	for (int bi = 0; bi < sizeof(small_arg_types)/sizeof(small_arg_types[0]); bi++)
	for (int yi = 0; yi < sizeof(arg_types)/sizeof(arg_types[0]); yi++)
	{
		std::string a_decl = small_arg_types[ai][0];
		strsubst(a_decl, "{dir}", "input");
		strsubst(a_decl, "{name}", "a");

		std::string b_decl = small_arg_types[bi][0];
		strsubst(b_decl, "{dir}", "input");
		strsubst(b_decl, "{name}", "b");

		std::string y_decl = arg_types[yi][0];
		strsubst(y_decl, "{dir}", "output");
		strsubst(y_decl, "{name}", "y");

		std::string a_ref = small_arg_types[ai][1];
		strsubst(a_ref, "{dir}", "input");
		strsubst(a_ref, "{name}", "a");

		std::string b_ref = small_arg_types[bi][1];
		strsubst(b_ref, "{dir}", "input");
		strsubst(b_ref, "{name}", "b");

		std::string y_ref = arg_types[yi][1];
		strsubst(y_ref, "{dir}", "output");
		strsubst(y_ref, "{name}", "y");

		char buffer[1024];
		snprintf(buffer, 1024, "rtl/concat_ops_%02d%02d%02d.v", ai, bi, yi);

		FILE *f = fopen(buffer, "w");
		fprintf(f, "module concat_ops_%02d%02d%02d(a, b, y);\n", ai, bi, yi);
		fprintf(f, "%s;\n", a_decl.c_str());
		fprintf(f, "%s;\n", b_decl.c_str());
		fprintf(f, "%s;\n", y_decl.c_str());
		fprintf(f, "assign %s = {%s, %s};\n", y_ref.c_str(), a_ref.c_str(), b_ref.c_str());
		fprintf(f, "endmodule\n");
		fclose(f);
	}
#endif

	return 0;
}

