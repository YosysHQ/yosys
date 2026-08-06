#include <gtest/gtest.h>

#include <chrono>
#include <cstdio>
#include <cstdlib>
#include <string>

#include <sys/resource.h>

#include "kernel/rtlil.h"
#include "kernel/yosys.h"

YOSYS_NAMESPACE_BEGIN

namespace {

int env_int(const char *name, int fallback)
{
	const char *value = getenv(name);
	if (value == nullptr || *value == 0)
		return fallback;
	return atoi(value);
}

size_t rss_bytes()
{
	size_t total_pages = 0, resident_pages = 0;
	FILE *f = fopen("/proc/self/statm", "r");
	if (f == nullptr)
		return 0;
	if (fscanf(f, "%zu %zu", &total_pages, &resident_pages) != 2)
		resident_pages = 0;
	fclose(f);
	return resident_pages * (size_t)sysconf(_SC_PAGESIZE);
}

size_t peak_rss_bytes()
{
	struct rusage ru;
	if (getrusage(RUSAGE_SELF, &ru) != 0)
		return 0;
	return (size_t)ru.ru_maxrss * 1024;
}

std::string name_padding;
bool attach_src = false;
int src_counter = 0;

void set_src(RTLIL::AttrObject *object)
{
	if (!attach_src)
		return;
	src_counter++;
	object->set_src_attribute(stringf("flatten_perf_source_file.v:%d.1-%d.20", src_counter, src_counter));
}

std::string pad(std::string name)
{
	name += name_padding;
	return name;
}

double ms(std::chrono::steady_clock::duration d)
{
	return std::chrono::duration<double, std::milli>(d).count();
}

RTLIL::Module *build_leaf(RTLIL::Design *design, int chain_length)
{
	RTLIL::Module *m = design->addModule(pad("\\flatten_perf_leaf_module"));

	RTLIL::Wire *in = m->addWire(pad("\\leaf_module_data_input_port"));
	in->port_input = true;
	set_src(in);
	RTLIL::Wire *out = m->addWire(pad("\\leaf_module_data_output_port"));
	out->port_output = true;
	set_src(out);
	m->fixup_ports();

	RTLIL::SigBit prev = in;
	for (int i = 0; i < chain_length; i++) {
		RTLIL::SigBit next = i + 1 == chain_length
			? RTLIL::SigBit(out)
			: RTLIL::SigBit(m->addWire(pad(stringf("\\leaf_intermediate_signal_wire_number_%d", i))));
		if (next.wire != nullptr)
			set_src(next.wire);
		set_src(m->addNotGate(pad(stringf("$leaf_inverter_cell_instance_number_%d", i)), prev, next));
		prev = next;
	}
	return m;
}

RTLIL::Module *build_level(RTLIL::Design *design, RTLIL::Module *child, int level, int branch)
{
	RTLIL::Module *m = design->addModule(pad(stringf("\\flatten_perf_hierarchy_level_%d_module", level)));

	RTLIL::Wire *in = m->addWire(pad(stringf("\\level_%d_module_data_input_port", level)));
	in->port_input = true;
	set_src(in);
	RTLIL::Wire *out = m->addWire(pad(stringf("\\level_%d_module_data_output_port", level)));
	out->port_output = true;
	set_src(out);
	m->fixup_ports();

	RTLIL::Wire *child_in = child->wire(child->ports.at(0));
	RTLIL::Wire *child_out = child->wire(child->ports.at(1));

	RTLIL::SigBit prev = in;
	for (int k = 0; k < branch; k++) {
		RTLIL::SigBit next = k + 1 == branch
			? RTLIL::SigBit(out)
			: RTLIL::SigBit(m->addWire(pad(stringf("\\level_%d_interconnect_signal_wire_number_%d", level, k))));
		RTLIL::Cell *cell = m->addCell(
			pad(stringf("\\hierarchical_child_instance_at_level_%d_branch_%d", level, k)), child->name);
		set_src(cell);
		cell->setPort(child_in->name, prev);
		cell->setPort(child_out->name, next);
		prev = next;
	}
	return m;
}

RTLIL::Module *build_design(RTLIL::Design *design, int depth, int branch, int chain_length)
{
	RTLIL::Module *m = build_leaf(design, chain_length);
	for (int level = depth - 1; level >= 0; level--)
		m = build_level(design, m, level, branch);
	m->set_bool_attribute(ID::top);
	return m;
}

} // namespace

TEST(FlattenPerf, deep_hierarchy_stress)
{
	int depth = env_int("YOSYS_FLATTEN_PERF_DEPTH", 8);
	int branch = env_int("YOSYS_FLATTEN_PERF_BRANCH", 2);
	int chain_length = env_int("YOSYS_FLATTEN_PERF_CHAIN", 48);
	int extra_name_chars = env_int("YOSYS_FLATTEN_PERF_NAMEPAD", 32);
	const char *flatten_args = getenv("YOSYS_FLATTEN_PERF_ARGS");

	ASSERT_GE(depth, 1);
	ASSERT_GE(branch, 2);
	ASSERT_GE(chain_length, 1);
	ASSERT_GE(extra_name_chars, 0);

	name_padding = std::string(extra_name_chars, 'n');
	attach_src = env_int("YOSYS_FLATTEN_PERF_SRC", 0) != 0;

	RTLIL::Design *design = new RTLIL::Design;

	auto build_start = std::chrono::steady_clock::now();
	RTLIL::Module *top = build_design(design, depth, branch, chain_length);
	auto build_end = std::chrono::steady_clock::now();

	size_t rss_before = rss_bytes();

	auto flatten_start = std::chrono::steady_clock::now();
	Pass::call(design, flatten_args != nullptr ? std::string("flatten ") + flatten_args : std::string("flatten"));
	auto flatten_end = std::chrono::steady_clock::now();

	size_t rss_after = rss_bytes();

	size_t leaves = 1;
	for (int level = 0; level < depth; level++)
		leaves *= (size_t)branch;

	EXPECT_EQ(design->modules().size(), 1u);
	EXPECT_EQ(design->top_module(), top);
	EXPECT_GE(top->cells().size(), leaves * (size_t)chain_length);

	printf("[ PERF     ] depth=%d branch=%d chain=%d namepad=%d src=%d args=%s leaves=%zu\n", depth, branch, chain_length,
			extra_name_chars, (int)attach_src, flatten_args != nullptr ? flatten_args : "", leaves);
	printf("[ PERF     ] cells=%zu wires=%zu\n", top->cells().size(), top->wires().size());
	printf("[ PERF     ] build_ms=%.1f flatten_ms=%.1f\n", ms(build_end - build_start), ms(flatten_end - flatten_start));
	printf("[ PERF     ] rss_before_mb=%.1f rss_after_mb=%.1f flatten_rss_mb=%.1f peak_rss_mb=%.1f\n",
			rss_before / 1048576.0, rss_after / 1048576.0,
			(rss_after - rss_before) / 1048576.0, peak_rss_bytes() / 1048576.0);
	fflush(stdout);

	delete design;
}

YOSYS_NAMESPACE_END
