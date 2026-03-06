/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2022  Miodrag Milanovic <micko@yosyshq.com>
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

#include "kernel/fstdata.h"

USING_YOSYS_NAMESPACE


static std::string file_base_name(std::string const & path)
{
	return path.substr(path.find_last_of("/\\") + 1);
}

FstData::FstData(std::string filename) : ctx(nullptr)
{
	#if !defined(YOSYS_DISABLE_SPAWN)
	std::string filename_trim = file_base_name(filename);
	if (filename_trim.size() > 4 && filename_trim.compare(filename_trim.size()-4, std::string::npos, ".vcd") == 0) {
		filename_trim.erase(filename_trim.size()-4);
		tmp_file = stringf("%s/converted_%s.fst", get_base_tmpdir(), filename_trim);
		std::string cmd = stringf("vcd2fst %s %s", filename, tmp_file);
		log("Exec: %s\n", cmd);
		if (run_command(cmd) != 0)
			log_cmd_error("Shell command failed!\n");
		filename = tmp_file;
	}
	#endif
	const std::vector<std::string> g_units = { "s", "ms", "us", "ns", "ps", "fs", "as", "zs" };
	ctx = (fstReaderContext *)fstReaderOpen(filename.c_str());
	if (!ctx)
		log_error("Error opening '%s' as FST file\n", filename);
	int scale = (int)fstReaderGetTimescale(ctx);	
	timescale = pow(10.0, scale);
	timescale_str = "";
	int unit = 0;
	int zeros = 0;
	if (scale > 0)  {
		zeros = scale;
	} else {
		if ((scale % 3) == 0) {
			zeros = (-scale % 3);
			unit = (-scale / 3);
		} else {
			zeros = 3 - (-scale % 3);
			unit = (-scale / 3) + 1;
		}
	}
	for (int i=0;i<zeros; i++) timescale_str += "0";
	timescale_str += g_units[unit];
	extractVarNames();
}

FstData::~FstData()
{
	if (ctx)
		fstReaderClose(ctx);
	if (!tmp_file.empty())
		remove(tmp_file.c_str());
}

uint64_t FstData::getStartTime() { return fstReaderGetStartTime(ctx); }

uint64_t FstData::getEndTime() { return fstReaderGetEndTime(ctx); }

static void normalize_brackets(std::string &str)
{
	for (auto &c : str) {
		if (c == '<')
			c = '[';
		else if (c == '>')
			c = ']';
	}
}

fstHandle FstData::getHandle(std::string name) { 
	normalize_brackets(name);
	if (name_to_handle.find(name) != name_to_handle.end())
		return name_to_handle[name];
	else 
		return 0;
};

dict<int,fstHandle> FstData::getMemoryHandles(std::string name) { 
	if (memory_to_handle.find(name) != memory_to_handle.end())
		return memory_to_handle[name];
	else 
		return dict<int,fstHandle>();
};

static std::string remove_spaces(std::string str)
{
	str.erase(std::remove(str.begin(), str.end(), ' '), str.end());
	return str;
}

void FstData::extractVarNames()
{
	struct fstHier *h;
	std::string fst_scope_name;

	// Track nested fork scopes using a stack to handle nested packed structs
	// Begins with outmost scope and ends with innermost scope
	// Scopes are not normalized on the stack
	std::vector<std::string> fork_scope_stack;

	// Start fork handles after the maximum real handle from FST file to avoid collisions
	fstHandle next_fork_handle = fstReaderGetMaxHandle(ctx) + 1;

	// Map of fork scopes to their members, which are all normalized
	std::map<std::string, std::vector<fstHandle>> fork_scopes;

	while ((h = fstReaderIterateHier(ctx))) {
		switch (h->htyp) {
			case FST_HT_SCOPE: {
				fst_scope_name = fstReaderPushScope(ctx, h->u.scope.name, NULL);

				// Fork scopes are identified by FST_ST_VCD_FORK and are pushed onto the stack
				if (h->u.scope.typ == FST_ST_VCD_FORK) {
					fork_scope_stack.push_back(fst_scope_name);
					// Create new vector that contains struct members
					normalize_brackets(fst_scope_name);
					fork_scopes[fst_scope_name] = std::vector<fstHandle>();
				}
				break;
			}
			case FST_HT_UPSCOPE: {
				if (!fork_scope_stack.empty() && fork_scope_stack.back() == fst_scope_name) {
					// Assign a unique handle to this fork scope and increment for future forks
					fstHandle fork_handle = next_fork_handle++;

					// Map normalized scope name to the handle for future lookups via getHandle()
					normalize_brackets(fst_scope_name);
					name_to_handle[fst_scope_name] = fork_handle;

					// Copy the extracted members of the fork scope to the fork scope members map
					// for value lookups in valueOf()
					fork_scope_members[fork_handle] = fork_scopes[fst_scope_name];

					// If this is a nested fork scope, add its handle to the parent fork scope
					if (fork_scope_stack.size() > 1) {
						std::string parent_fork = fork_scope_stack[fork_scope_stack.size() - 2];
						normalize_brackets(parent_fork);
						fork_scopes[parent_fork].push_back(fork_handle);
					}

					// Pop this fork scope from the stack
					fork_scope_stack.pop_back();
				}
				fst_scope_name = fstReaderPopScope(ctx);
				break;
			}
			case FST_HT_VAR: {
				FstVar var;
				var.id = h->u.var.handle;
				var.is_alias = h->u.var.is_alias;
				var.is_reg = (fstVarType)h->u.var.typ == FST_VT_VCD_REG;
				var.name = remove_spaces(h->u.var.name);
				var.scope = fst_scope_name;
				normalize_brackets(var.scope);
				var.width = h->u.var.length;
				vars.push_back(var);
				if (!var.is_alias)
					handle_to_var[h->u.var.handle] = var;

				// Add variable to the innermost fork scope in the fork scope stack
				if (!fork_scope_stack.empty()) {
					std::string current_fork = fork_scope_stack.back();
					normalize_brackets(current_fork);
					fork_scopes[current_fork].push_back(h->u.var.handle);
				}

				std::string clean_name;
				bool has_space = false;
				for(size_t i=0;i<strlen(h->u.var.name);i++) 
				{
					char c = h->u.var.name[i];
					if(c==' ') { has_space = true; break; }
					clean_name += c;
				}
				if (clean_name[0]=='\\')
					clean_name = clean_name.substr(1);
				if (!has_space) {
					size_t pos = clean_name.find_last_of("[");
					std::string index_or_range = clean_name.substr(pos+1);
					if (index_or_range.find(":") != std::string::npos) {
						clean_name = clean_name.substr(0,pos);
					}
				}
				size_t pos = clean_name.find_last_of("<");
				if (pos != std::string::npos && clean_name.back() == '>') {
					std::string mem_cell = clean_name.substr(0, pos);
					normalize_brackets(mem_cell);
					std::string addr = clean_name.substr(pos+1);
					addr.pop_back(); // remove closing bracket
					char *endptr;
					int mem_addr = strtol(addr.c_str(), &endptr, 16);
					if (*endptr) {
						log_debug("Error parsing memory address in : %s\n", clean_name);
					} else {
						memory_to_handle[var.scope+"."+mem_cell][mem_addr] = var.id;
					}
				}
				pos = clean_name.find_last_of("[");
				if (pos != std::string::npos && clean_name.back() == ']') {
					std::string mem_cell = clean_name.substr(0, pos);
					normalize_brackets(mem_cell);
					std::string addr = clean_name.substr(pos+1);
					addr.pop_back(); // remove closing bracket
					char *endptr;
					int mem_addr = strtol(addr.c_str(), &endptr, 10);
					if (*endptr) {
						log_debug("Error parsing memory address in : %s\n", clean_name);
					} else {
						memory_to_handle[var.scope+"."+mem_cell][mem_addr] = var.id;
					}
				}
				normalize_brackets(clean_name);
				name_to_handle[var.scope+"."+clean_name] = h->u.var.handle;
				break;
			}
		}
	}
}


static void reconstruct_clb_varlen_attimes(void *user_data, uint64_t pnt_time, fstHandle pnt_facidx, const unsigned char *pnt_value, uint32_t plen)
{
	FstData *ptr = (FstData*)user_data;
	ptr->reconstruct_callback_attimes(pnt_time, pnt_facidx, pnt_value, plen);
}

static void reconstruct_clb_attimes(void *user_data, uint64_t pnt_time, fstHandle pnt_facidx, const unsigned char *pnt_value)
{
	FstData *ptr = (FstData*)user_data;
	uint32_t plen = (pnt_value) ?  strlen((const char *)pnt_value) : 0;
	ptr->reconstruct_callback_attimes(pnt_time, pnt_facidx, pnt_value, plen);
}

void FstData::reconstruct_callback_attimes(uint64_t pnt_time, fstHandle pnt_facidx, const unsigned char *pnt_value, uint32_t /* plen */)
{
	if (pnt_time > end_time || !pnt_value) return;
	if (curr_cycle > last_cycle) return;
	// if we are past the timestamp
	bool is_clock = false;
	if (!all_samples) {
		for(auto &s : clk_signals) {
			if (s==pnt_facidx)  { 
				is_clock=true;
				break;
			}
		}
	}

	if (pnt_time > past_time) {
		past_data = last_data;
		past_time = pnt_time;
	}

	if (pnt_time > last_time) {
		if (all_samples) {
			callback(last_time);
			curr_cycle++;
			last_time = pnt_time;
		} else {
			if (is_clock) {
				std::string val = std::string((const char *)pnt_value);
				std::string prev = past_data[pnt_facidx];
				if ((prev!="1" && val=="1") || (prev!="0" && val=="0")) {
					callback(last_time);
					curr_cycle++;
					last_time = pnt_time;
				}
			}
		}
	}
	// always update last_data
	last_data[pnt_facidx] =  std::string((const char *)pnt_value);
}

void FstData::reconstructAllAtTimes(std::vector<fstHandle> &signal, uint64_t start, uint64_t end, unsigned int end_cycle, CallbackFunction cb)
{
	clk_signals = signal;
	callback = cb;
	start_time = start;
	end_time = end;
	curr_cycle = 0;
	last_cycle = end_cycle;
	last_data.clear();
	last_time = start_time;
	past_data.clear();
	past_time = start_time;
	all_samples = clk_signals.empty();

	fstReaderSetUnlimitedTimeRange(ctx);
	fstReaderSetFacProcessMaskAll(ctx);
	fstReaderIterBlocks2(ctx, reconstruct_clb_attimes, reconstruct_clb_varlen_attimes, this, nullptr);
	if (last_time!=end_time && curr_cycle <= last_cycle) {
		past_data = last_data;
		callback(last_time);
		curr_cycle++;
	}
	if (curr_cycle <= last_cycle) {
		past_data = last_data;
		callback(end_time);
		curr_cycle++;
	}
}

std::string FstData::valueOf(fstHandle signal)
{
	// Check if this is a fork scope (struct)
	auto it = fork_scope_members.find(signal);
	if (it != fork_scope_members.end()) {
		std::string result;
		const std::vector<fstHandle>& members = it->second;

		// Iterate over members of the struct to get concatenated value.
		// The first declared member is MSB in SystemVerilog packed structs
		for (auto m = members.begin(); m != members.end(); m++) {
			fstHandle member = *m;
			std::string member_val;
			
			// Check if this member is itself a nested fork scope (struct)
			if (fork_scope_members.find(member) != fork_scope_members.end()) {
				// Recursively get the value of the nested struct
				member_val = valueOf(member);
			} else {
				// Regular variable - look up in past_data
				int expected_width = 0;

				// Get the declared width of this member
				if (handle_to_var.find(member) != handle_to_var.end()) {
					expected_width = handle_to_var[member].width;
				}
				// Get the current value of the member
				if (past_data.find(member) != past_data.end()) {
					member_val = past_data[member];
					// Pad with zeros to the expected width of the member
					if (expected_width > 0 && (int)member_val.length() < expected_width) {
						member_val = std::string(expected_width - member_val.length(), '0') + member_val;
					}
				} else if (expected_width > 0) {
					// No value yet, use X to pad
					member_val = std::string(expected_width, 'x');
				} else { // fallback to X
					member_val = "x";
				}
			}
			// Concatenate the member value to the overall struct value
			result += member_val;
		}
		return result;
	}
	
	// Normal signal handling
	if (past_data.find(signal) == past_data.end()) {
		return std::string(handle_to_var[signal].width, 'x');
	}
	return past_data[signal];
}

int FstData::getWidth(fstHandle signal)
{
	// Check if signal is a fork scope (struct)
	if (fork_scope_members.count(signal)) {
		// Sum the widths of all members of the fork scope, which may be forks themselves
		int width = 0;
		for (fstHandle member : fork_scope_members[signal]) {
			width += getWidth(member);
		}
		return width;
	}

	if (handle_to_var.count(signal)) {
		return handle_to_var[signal].width;
	}
	
	// Signal not found
	log_warning("Signal %d was not extracted from file...\n", signal);
	return 0;
}

// Auto-discover scope from FST by finding the top module
std::string FstData::autoScope(Module *topmod) {

	log("Auto-discovering scopes from file...\n");
	std::string top = RTLIL::unescape_id(topmod->name);
	std::string scope = "";

	// Map top module port name to their bit widths (RTL reference point)
	dict<std::string, int> top2widths;
	for (auto wire : topmod->wires()) {
		if (wire->port_input || wire->port_output) {
			top2widths[RTLIL::unescape_id(wire->name)] = wire->width;
		}
	}
	log("Extracted %d ports from top module\n", GetSize(top2widths));

	// For each scope, track the number of matching ports
	dict<std::string, int> scopes2matches;

	// Use name_to_handle to get all signals from the FST file
	for (auto entry : name_to_handle) {
		std::string name = entry.first;
		fstHandle handle = entry.second;

		// Extract signal name and scope using '.'
		// Signal names of form '{scope}.signal_name' with scope potentially
		// having zero to multiple '.'
		size_t last_dot = name.find_last_of('.');
		if (last_dot != std::string::npos) { // no '.' means no scope/signal extraction is possible
			std::string scope = name.substr(0, last_dot);
			std::string signal_name = name.substr(last_dot + 1);

			// Check that signal is in the top module and width matches
			if (top2widths.count(signal_name)) {
				int signal_width = getWidth(handle);
				if (signal_width == top2widths[signal_name]) {
					scopes2matches[scope]++;
				}
			}
		}
	}

	// Find scopes with exact matches and add to array
	std::vector<std::string> results;
	for (const auto& entry : scopes2matches) {
		int num_matches = entry.second;
		if (num_matches == GetSize(top2widths)) {
			std::string scope = entry.first;
			results.push_back(scope);
		}
	}
	if (results.empty()) {
		log_warning("Could not auto-discover scope for module '%s'...\n", 
			RTLIL::unescape_id(topmod->name).c_str());
		return "";
	} else {
		log("Found %d scopes for module '%s':\n", GetSize(results), RTLIL::unescape_id(topmod->name).c_str());
		for (const auto& scope : results) {
			log("  %s\n", scope.c_str());
		}
		if (results.size() > 1) {
			log_warning("Multiple scopes found for module '%s'. Using the first one.\n", 
				RTLIL::unescape_id(topmod->name).c_str());
		}
		std::string scope = results[0];
	}
	return scope;
}
