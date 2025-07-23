/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2024  Emily Schmidt <emily@yosyshq.com>
 *  Copyright (C) 2024 National Technology and Engineering Solutions of Sandia, LLC
 *
 *  Permission to use, copy, modify, and/or distribute this software for any
 *  purpose with or without fee is hereby granted, provided that the above
 *  copyright notice and this permission notice appear in all copies.
 *
 *  THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 *  WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 *  MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 *  ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 *  WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 *  ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 *  OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *
 */

#include "kernel/yosys.h"
#include "kernel/functional.h"
#include <random>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct MemContentsTest {
	int addr_width, data_width;
	MemContents state;
	using addr_t = MemContents::addr_t;
	std::map<addr_t, RTLIL::Const> reference;
	MemContentsTest(int addr_width, int data_width) : addr_width(addr_width), data_width(data_width), state(addr_width, data_width, RTLIL::Const(State::S0, data_width))  {}
	void check() {
		state.check();
		for(auto addr = 0; addr < (1<<addr_width); addr++) {
			auto it = reference.find(addr);
			if(it != reference.end()) {
				if(state.count_range(addr, addr + 1) != 1) goto error;
				if(it->second != state[addr]) goto error;
			} else {
				if(state.count_range(addr, addr + 1) != 0) goto error;
			}
		}
		return;
		error:
		printf("FAIL\n");
		int digits = (data_width + 3) / 4;
		
		for(auto addr = 0; addr < (1<<addr_width); addr++) {
			if(addr % 8 == 0) printf("%.8x   ", addr);
			auto it = reference.find(addr);
			bool ref_def = it != reference.end();
			RTLIL::Const ref_value = ref_def ? it->second : state.default_value();
			std::string ref_string = stringf("%.*x", digits, ref_value.as_int());
			bool sta_def = state.count_range(addr, addr + 1) == 1;
			RTLIL::Const sta_value = state[addr];
			std::string sta_string = stringf("%.*x", digits, sta_value.as_int());
			if(ref_def && sta_def) {
				if(ref_value == sta_value) printf("%s%s", ref_string.c_str(), string(digits, ' ').c_str());
				else printf("%s%s", ref_string.c_str(), sta_string.c_str());
			} else if(ref_def) {
				printf("%s%s", ref_string.c_str(), string(digits, 'M').c_str());
			} else if(sta_def) {
				printf("%s%s", sta_string.c_str(), string(digits, 'X').c_str());
			} else {
				printf("%s", string(2*digits, ' ').c_str());
			}
			printf(" ");
			if(addr % 8 == 7) printf("\n");
		}
		printf("\n");
		//log_abort();
	}
	void clear_range(addr_t begin_addr, addr_t end_addr) {
		for(auto addr = begin_addr; addr != end_addr; addr++)
			reference.erase(addr);
		state.clear_range(begin_addr, end_addr);
		check();
	}
	void insert_concatenated(addr_t addr, RTLIL::Const const &values) {
		addr_t words = ((addr_t) values.size() + data_width - 1) / data_width;
		for(addr_t i = 0; i < words; i++) {
			reference.erase(addr + i);
			reference.emplace(addr + i, values.extract(i * data_width, data_width));
		}
		state.insert_concatenated(addr, values);
		check();
	}
	template<typename Rnd> void run(Rnd &rnd, int n) {
		std::uniform_int_distribution<addr_t> addr_dist(0, (1<<addr_width) - 1);
		std::poisson_distribution<addr_t> length_dist(10);
		std::uniform_int_distribution<uint64_t> data_dist(0, ((uint64_t)1<<data_width) - 1);
		while(n-- > 0) {
			addr_t low = addr_dist(rnd);
			//addr_t length = std::min((1<<addr_width) - low, length_dist(rnd));
			//addr_t high = low + length - 1;
			addr_t high = addr_dist(rnd);
			if(low > high) std::swap(low, high);
			if((rnd() & 7) == 0) {
				log_debug("clear %.2x to %.2x\n", (int)low, (int)high);
				clear_range(low, high + 1);
			} else {
				log_debug("insert %.2x to %.2x\n", (int)low, (int)high);
				RTLIL::Const values;
				for(addr_t addr = low; addr <= high; addr++) {
					RTLIL::Const word(data_dist(rnd), data_width);
					values.bits().insert(values.bits().end(), word.begin(), word.end());
				}
				insert_concatenated(low, values);
			}
		}
	}

};

struct FunctionalTestGeneric : public Pass
{
	FunctionalTestGeneric() : Pass("test_generic", "test the generic compute graph") {}

    void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("TODO: add help message\n");
		log("\n");
    }

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
        log_header(design, "Executing Test Generic.\n");

		size_t argidx = 1;
		extra_args(args, argidx, design);
/*
		MemContentsTest test(8, 16);

		std::random_device seed_dev;
		std::mt19937 rnd(23); //seed_dev());
		test.run(rnd, 1000);
*/

		for (auto module : design->selected_modules()) {
            log("Dumping module `%s'.\n", module->name.c_str());
			auto fir = Functional::IR::from_module(module);
			for(auto node : fir)
				std::cout << RTLIL::unescape_id(node.name()) << " = " << node.to_string([](auto n) { return RTLIL::unescape_id(n.name()); }) << "\n";
			for(auto output : fir.all_outputs())
				std::cout << RTLIL::unescape_id(output->kind) << " " << RTLIL::unescape_id(output->name) << " = " << RTLIL::unescape_id(output->value().name()) << "\n";
			for(auto state : fir.all_states())
				std::cout << RTLIL::unescape_id(state->kind) << " " << RTLIL::unescape_id(state->name) << " = " << RTLIL::unescape_id(state->next_value().name()) << "\n";
		}
	}
} FunctionalCxxBackend;

PRIVATE_NAMESPACE_END
