
#define GENERATE_BINARY_OPS
#define GENERATE_UNARY_OPS
#define GENERATE_TERNARY_OPS
#define GENERATE_CONCAT_OPS
#undef  GENERATE_REPEAT_OPS  // disabled because of XST bug
#define GENERATE_EXPRESSIONS

#include <sys/stat.h>
#include <sys/types.h>
#include <string.h>
#include <stdint.h>
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

uint32_t xorshift32(uint32_t seed = 0) {
	static uint32_t x = 314159265;
	if (seed)
		x = seed;
	x ^= x << 13;
	x ^= x >> 17;
	x ^= x << 5;
	return x;
}

void print_expression(FILE *f, int budget, uint32_t mask = 0)
{
	size_t num_binary_ops = sizeof(binary_ops)/sizeof(*binary_ops);
	size_t num_unary_ops = sizeof(unary_ops)/sizeof(*unary_ops);
	size_t num_arg_types = sizeof(arg_types)/sizeof(*arg_types);
	int i, j, k, mode;

	if (budget == 0) {
		fprintf(f, "%c%d", 'a' + char(xorshift32() % 2), int(xorshift32() % num_arg_types));
		return;
	}

	int num_modes = 4;
	while ((mask & ~((~0) << num_modes)) == 0)
		mask = xorshift32();
	do {
		mode = xorshift32() % num_modes;
	} while (((1 << mode) & mask) == 0);
	// fprintf(f, "/* %d */", mode);

	budget--;
	switch (mode)
	{
	case 0:
		fprintf(f, "(");
		print_expression(f, budget, mask);
		fprintf(f, ")");
		break;
	case 1:
		fprintf(f, "(");
		print_expression(f, budget/2, mask);
	#if 1
		// FIXME: relational operators disabled because there is an xst bug..
		do k = xorshift32() % num_binary_ops; while ((k >= 9 && k <= 12) || (k >= 3 && k <= 6));
		fprintf(f, "%s", binary_ops[k]);
	#else
		fprintf(f, "%s", binary_ops[xorshift32() % num_binary_ops]);
	#endif
		print_expression(f, budget/2, mask);
		fprintf(f, ")");
		break;
	case 2:
		fprintf(f, "(%s", unary_ops[xorshift32() % num_unary_ops]);
		print_expression(f, budget, mask);
		fprintf(f, ")");
		break;
	case 3:
		i = 1 + xorshift32() % 3;
		fprintf(f, "{");
		for (j = 0; j < i; j++) {
			if (j)
				fprintf(f, ",");
			print_expression(f, budget / i, mask);
		}
		fprintf(f, "}");
		break;
#if 0
		// FIXME: disabled because there is an xst bug..
	case 4:
		i = xorshift32() % 4;
		fprintf(f, "{%d{", i);
		print_expression(f, budget, mask);
		fprintf(f, "}}");
		break;
#endif
	}
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

#ifdef GENERATE_REPEAT_OPS
	for (int a = 0; a < 4; a++)
	for (int bi = 0; bi < sizeof(small_arg_types)/sizeof(small_arg_types[0]); bi++)
	for (int yi = 0; yi < sizeof(arg_types)/sizeof(arg_types[0]); yi++)
	{
		std::string b_decl = small_arg_types[bi][0];
		strsubst(b_decl, "{dir}", "input");
		strsubst(b_decl, "{name}", "b");

		std::string y_decl = arg_types[yi][0];
		strsubst(y_decl, "{dir}", "output");
		strsubst(y_decl, "{name}", "y");

		std::string b_ref = small_arg_types[bi][1];
		strsubst(b_ref, "{dir}", "input");
		strsubst(b_ref, "{name}", "b");

		std::string y_ref = arg_types[yi][1];
		strsubst(y_ref, "{dir}", "output");
		strsubst(y_ref, "{name}", "y");

		char buffer[1024];
		snprintf(buffer, 1024, "rtl/repeat_ops_%02d%02d%02d.v", a, bi, yi);

		FILE *f = fopen(buffer, "w");
		fprintf(f, "module repeat_ops_%02d%02d%02d(a, b, y);\n", a, bi, yi);
		fprintf(f, "input a;\n");
		fprintf(f, "%s;\n", b_decl.c_str());
		fprintf(f, "%s;\n", y_decl.c_str());
		fprintf(f, "assign %s = {%d{%s}};\n", y_ref.c_str(), a, b_ref.c_str());
		fprintf(f, "endmodule\n");
		fclose(f);
	}
#endif

#ifdef GENERATE_EXPRESSIONS
	for (int i = 0; i < 1000; i++)
	{
		xorshift32(1234 + i);
		xorshift32();
		xorshift32();
		xorshift32();

		char buffer[1024];
		snprintf(buffer, 1024, "rtl/expression_%05d.v", i);

		FILE *f = fopen(buffer, "w");
		fprintf(f, "module expression_%05d(a, b, y);\n", i);

		for (char var = 'a'; var <= 'y'; var++)
		{
			fprintf(f, "%s [", var != 'y' ? "input" : "output");
			for (int j = 0; j < sizeof(arg_types)/sizeof(arg_types[0]); j++)
				fprintf(f, "%s%s", j ? "+" : "", arg_types[j][2]);
			fprintf(f, "-1:0] %c;\n", var);

			for (int j = 0; j < sizeof(arg_types)/sizeof(arg_types[0]); j++)
			{
				std::string decl = arg_types[j][0];
				strsubst(decl, "{dir}", "wire");
				snprintf(buffer, 1024, "%c%d", var, j);
				strsubst(decl, "{name}", buffer);

				if (var != 'y') {
					fprintf(f, "%s = %c[", decl.c_str(), var);
					for (int k = 0; k <= j; k++)
						fprintf(f, "%s%s", k ? "+" : "", arg_types[k][2]);
					fprintf(f, "-1:");
					for (int k = 0; k < j; k++)
						fprintf(f, "%s%s", k ? "+" : "", arg_types[k][2]);
					fprintf(f, "%s];\n", j ? "" : "0");
				} else
					fprintf(f, "%s;\n", decl.c_str());
			}

			if (var == 'b')
				var = 'x';
		}

		fprintf(f, "assign y = {");
		for (int j = 0; j < sizeof(arg_types)/sizeof(arg_types[0]); j++)
			fprintf(f, "%sy%d", j ? "," : "", j);
		fprintf(f, "};\n");

		for (int j = 0; j < sizeof(arg_types)/sizeof(arg_types[0]); j++) {
			fprintf(f, "assign y%d = ", j);
			print_expression(f, 1 + xorshift32() % 20);
			fprintf(f, ";\n");
		}

		fprintf(f, "endmodule\n");
		fclose(f);
	}
#endif

	return 0;
}

