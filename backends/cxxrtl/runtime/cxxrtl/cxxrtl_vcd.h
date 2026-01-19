/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2020  whitequark <whitequark@whitequark.org>
 *
 *  Permission to use, copy, modify, and/or distribute this software for any
 *  purpose with or without fee is hereby granted.
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

#ifndef CXXRTL_VCD_H
#define CXXRTL_VCD_H

#include <cxxrtl/cxxrtl.h>

namespace cxxrtl {

class vcd_writer {
	struct variable {
		size_t ident;
		size_t width;
		chunk_t *curr;
		size_t cache_offset;
		debug_outline *outline;
		bool *outline_warm;
	};

	std::vector<std::string> current_scope;
	std::map<debug_outline*, bool> outlines;
	std::vector<variable> variables;
	std::vector<chunk_t> cache;
	std::map<chunk_t*, size_t> aliases;
	bool streaming = false;

	void emit_timescale(unsigned number, const std::string &unit) {
		assert(!streaming);
		assert(number == 1 || number == 10 || number == 100);
		assert(unit == "s" || unit == "ms" || unit == "us" ||
		       unit == "ns" || unit == "ps" || unit == "fs");
		buffer += "$timescale " + std::to_string(number) + " " + unit + " $end\n";
	}

	void emit_scope(const std::vector<std::string> &scope) {
		assert(!streaming);
		size_t same_scope_count = 0;
		while ((same_scope_count < current_scope.size()) &&
			   (same_scope_count < scope.size()) &&
			   (current_scope[same_scope_count] == scope[same_scope_count])) {
			same_scope_count++;
		}
		while (current_scope.size() > same_scope_count) {
			buffer += "$upscope $end\n";
			current_scope.pop_back();
		}
		while (current_scope.size() < scope.size()) {
			buffer += "$scope module " + scope[current_scope.size()] + " $end\n";
			current_scope.push_back(scope[current_scope.size()]);
		}
	}

	void emit_ident(size_t ident) {
		do {
			buffer += '!' + ident % 94; // "base94"
			ident /= 94;
		} while (ident != 0);
	}

	void emit_name(const std::string &name) {
		for (char c : name) {
			if (c == ':') {
				// Due to a bug, GTKWave cannot parse a colon in the variable name, causing the VCD file
				// to be unreadable. It cannot be escaped either, so replace it with the sideways colon.
				buffer += "..";
			} else {
				buffer += c;
			}
		}
	}

	void emit_var(const variable &var, const std::string &type, const std::string &name,
	              size_t lsb_at, bool multipart) {
		assert(!streaming);
		buffer += "$var " + type + " " + std::to_string(var.width) + " ";
		emit_ident(var.ident);
		buffer += " ";
		emit_name(name);
		if (multipart || name.back() == ']' || lsb_at != 0) {
			if (var.width == 1)
				buffer += " [" + std::to_string(lsb_at) + "]";
			else
				buffer += " [" + std::to_string(lsb_at + var.width - 1) + ":" + std::to_string(lsb_at) + "]";
		}
		buffer += " $end\n";
	}

	void emit_enddefinitions() {
		assert(!streaming);
		buffer += "$enddefinitions $end\n";
		streaming = true;
	}

	void emit_time(uint64_t timestamp) {
		assert(streaming);
		buffer += "#" + std::to_string(timestamp) + "\n";
	}

	void emit_scalar(const variable &var) {
		assert(streaming);
		assert(var.width == 1);
		buffer += (*var.curr ? '1' : '0');
		emit_ident(var.ident);
		buffer += '\n';
	}

	void emit_vector(const variable &var) {
		assert(streaming);
		buffer += 'b';
		for (size_t bit = var.width - 1; bit != (size_t)-1; bit--) {
			bool bit_curr = var.curr[bit / (8 * sizeof(chunk_t))] & (1 << (bit % (8 * sizeof(chunk_t))));
			buffer += (bit_curr ? '1' : '0');
		}
		if (var.width == 0)
			buffer += '0';
		buffer += ' ';
		emit_ident(var.ident);
		buffer += '\n';
	}

	void reset_outlines() {
		for (auto &outline_it : outlines)
			outline_it.second = /*warm=*/(outline_it.first == nullptr);
	}

	variable &register_variable(size_t width, chunk_t *curr, bool constant = false, debug_outline *outline = nullptr) {
		if (aliases.count(curr)) {
			return variables[aliases[curr]];
		} else {
			auto outline_it = outlines.emplace(outline, /*warm=*/(outline == nullptr)).first;
			const size_t chunks = (width + (sizeof(chunk_t) * 8 - 1)) / (sizeof(chunk_t) * 8);
			aliases[curr] = variables.size();
			if (constant) {
				variables.emplace_back(variable { variables.size(), width, curr, (size_t)-1, outline_it->first, &outline_it->second });
			} else {
				variables.emplace_back(variable { variables.size(), width, curr, cache.size(), outline_it->first, &outline_it->second });
				cache.insert(cache.end(), &curr[0], &curr[chunks]);
			}
			return variables.back();
		}
	}

	bool test_variable(const variable &var) {
		if (var.cache_offset == (size_t)-1)
			return false; // constant
		if (!*var.outline_warm) {
			var.outline->eval();
			*var.outline_warm = true;
		}
		const size_t chunks = (var.width + (sizeof(chunk_t) * 8 - 1)) / (sizeof(chunk_t) * 8);
		if (std::equal(&var.curr[0], &var.curr[chunks], &cache[var.cache_offset])) {
			return false;
		} else {
			std::copy(&var.curr[0], &var.curr[chunks], &cache[var.cache_offset]);
			return true;
		}
	}

	static std::vector<std::string> split_hierarchy(const std::string &hier_name) {
		std::vector<std::string> hierarchy;
		size_t prev = 0;
		while (true) {
			size_t curr = hier_name.find_first_of(' ', prev);
			if (curr == std::string::npos) {
				hierarchy.push_back(hier_name.substr(prev));
				break;
			} else {
				hierarchy.push_back(hier_name.substr(prev, curr - prev));
				prev = curr + 1;
			}
		}
		return hierarchy;
	}

public:
	std::string buffer;

	void timescale(unsigned number, const std::string &unit) {
		emit_timescale(number, unit);
	}

	void add(const std::string &hier_name, const debug_item &item, bool multipart = false) {
		std::vector<std::string> scope = split_hierarchy(hier_name);
		std::string name = scope.back();
		scope.pop_back();

		emit_scope(scope);
		switch (item.type) {
			// Not the best naming but oh well...
			case debug_item::VALUE:
				emit_var(register_variable(item.width, item.curr, /*constant=*/item.next == nullptr),
				         "wire", name, item.lsb_at, multipart);
				break;
			case debug_item::WIRE:
				emit_var(register_variable(item.width, item.curr),
				         "reg", name, item.lsb_at, multipart);
				break;
			case debug_item::MEMORY: {
				const size_t stride = (item.width + (sizeof(chunk_t) * 8 - 1)) / (sizeof(chunk_t) * 8);
				for (size_t index = 0; index < item.depth; index++) {
					chunk_t *nth_curr = &item.curr[stride * index];
					std::string nth_name = name + '[' + std::to_string(index) + ']';
					emit_var(register_variable(item.width, nth_curr),
					         "reg", nth_name, item.lsb_at, multipart);
				}
				break;
			}
			case debug_item::ALIAS:
				// Like VALUE, but, even though `item.next == nullptr` always holds, the underlying value
				// can actually change, and must be tracked. In most cases the VCD identifier will be
				// unified with the aliased reg, but we should handle the case where only the alias is
				// added to the VCD writer, too.
				emit_var(register_variable(item.width, item.curr),
				         "wire", name, item.lsb_at, multipart);
				break;
			case debug_item::OUTLINE:
				emit_var(register_variable(item.width, item.curr, /*constant=*/false, item.outline),
				         "wire", name, item.lsb_at, multipart);
				break;
		}
	}

	template<class Filter>
	void add(const debug_items &items, const Filter &filter) {
		// `debug_items` is a map, so the items are already sorted in an order optimal for emitting
		// VCD scope sections.
		for (auto &it : items.table)
			for (auto &part : it.second)
				if (filter(it.first, part))
					add(it.first, part, it.second.size() > 1);
	}

	void add(const debug_items &items) {
		this->add(items, [](const std::string &, const debug_item &) {
			return true;
		});
	}

	void add_without_memories(const debug_items &items) {
		this->add(items, [](const std::string &, const debug_item &item) {
			return item.type != debug_item::MEMORY;
		});
	}

	void sample(uint64_t timestamp) {
		bool first_sample = !streaming;
		if (first_sample) {
			emit_scope({});
			emit_enddefinitions();
		}
		reset_outlines();
		emit_time(timestamp);
		for (auto var : variables)
			if (test_variable(var) || first_sample) {
				if (var.width == 1)
					emit_scalar(var);
				else
					emit_vector(var);
			}
	}
};

}

#endif
