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
		tmp_file = stringf("%s/converted_%s.fst", get_base_tmpdir().c_str(), filename_trim.c_str());
		std::string cmd = stringf("vcd2fst %s %s", filename.c_str(), tmp_file.c_str());
		log("Exec: %s\n", cmd.c_str());
		if (run_command(cmd) != 0)
			log_cmd_error("Shell command failed!\n");
		filename = tmp_file;
	}
	#endif
	const std::vector<std::string> g_units = { "s", "ms", "us", "ns", "ps", "fs", "as", "zs" };
	ctx = (fstReaderContext *)fstReaderOpen(filename.c_str());
	if (!ctx)
		log_error("Error opening '%s' as FST file\n", filename.c_str());
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

	while ((h = fstReaderIterateHier(ctx))) {
		switch (h->htyp) {
			case FST_HT_SCOPE: {
				fst_scope_name = fstReaderPushScope(ctx, h->u.scope.name, NULL);
				break;
			}
			case FST_HT_UPSCOPE: {
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
				std::string clean_name;
				for(size_t i=0;i<strlen(h->u.var.name);i++) 
				{
					char c = h->u.var.name[i];
					if(c==' ') break;
					clean_name += c;
				}
				if (clean_name[0]=='\\')
					clean_name = clean_name.substr(1);
				size_t pos = clean_name.find_last_of("<");
				if (pos != std::string::npos && clean_name.back() == '>') {
					std::string mem_cell = clean_name.substr(0, pos);
					normalize_brackets(mem_cell);
					std::string addr = clean_name.substr(pos+1);
					addr.pop_back(); // remove closing bracket
					char *endptr;
					int mem_addr = strtol(addr.c_str(), &endptr, 16);
					if (*endptr) {
						log_debug("Error parsing memory address in : %s\n", clean_name.c_str());
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
						log_debug("Error parsing memory address in : %s\n", clean_name.c_str());
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
			last_time = pnt_time;
		} else {
			if (is_clock) {
				std::string val = std::string((const char *)pnt_value);
				std::string prev = past_data[pnt_facidx];
				if ((prev!="1" && val=="1") || (prev!="0" && val=="0")) {
					callback(last_time);
					last_time = pnt_time;
				}
			}
		}
	}
	// always update last_data
	last_data[pnt_facidx] =  std::string((const char *)pnt_value);
}

void FstData::reconstructAllAtTimes(std::vector<fstHandle> &signal, uint64_t start, uint64_t end, CallbackFunction cb)
{
	clk_signals = signal;
	callback = cb;
	start_time = start;
	end_time = end;
	last_data.clear();
	last_time = start_time;
	past_data.clear();
	past_time = start_time;
	all_samples = clk_signals.empty();

	fstReaderSetUnlimitedTimeRange(ctx);
	fstReaderSetFacProcessMaskAll(ctx);
	fstReaderIterBlocks2(ctx, reconstruct_clb_attimes, reconstruct_clb_varlen_attimes, this, nullptr);
	if (last_time!=end_time) {
		past_data = last_data;
		callback(last_time);
	}
	past_data = last_data;
	callback(end_time);
}

std::string FstData::valueOf(fstHandle signal)
{
	if (past_data.find(signal) == past_data.end())
		log_error("Signal id %d not found\n", (int)signal);
	return past_data[signal];
}
