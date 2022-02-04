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


FstData::FstData(std::string filename) : ctx(nullptr)
{
	const std::vector<std::string> g_units = { "s", "ms", "us", "ns", "ps", "fs", "as", "zs" };
	ctx = (fstReaderContext *)fstReaderOpen(filename.c_str());
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
}

uint64_t FstData::getStartTime() { return fstReaderGetStartTime(ctx); }

uint64_t FstData::getEndTime() { return fstReaderGetEndTime(ctx); }

fstHandle FstData::getHandle(std::string name) { 
	if (name_to_handle.find(name) != name_to_handle.end())
		return name_to_handle[name];
	else 
		return 0;
};

static std::string remove_spaces(std::string str)
{
	str.erase(std::remove(str.begin(), str.end(), ' '), str.end());
	return str;
}

void FstData::extractVarNames()
{
	struct fstHier *h;
	intptr_t snum = 0;

	while ((h = fstReaderIterateHier(ctx))) {
		switch (h->htyp) {
			case FST_HT_SCOPE: {
				snum++;
				std::string fst_scope_name = fstReaderPushScope(ctx, h->u.scope.name, (void *)(snum));
				scopes.push_back(fst_scope_name);
				break;
			}
			case FST_HT_UPSCOPE: {
				fstReaderPopScope(ctx);
				snum = fstReaderGetCurrentScopeLen(ctx) ? (intptr_t)fstReaderGetCurrentScopeUserInfo(ctx) : 0;
				break;
			}
			case FST_HT_VAR: {
				FstVar var;
				var.id = h->u.var.handle;
				var.is_alias = h->u.var.is_alias;
				var.name = remove_spaces(h->u.var.name);
				var.scope = scopes.back();
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
				//log("adding %s.%s\n",var.scope.c_str(), clean_name.c_str());
				
				name_to_handle[var.scope+"."+clean_name] = h->u.var.handle;
				break;
			}
		}
	}
}

static void reconstruct_edges_varlen(void *user_data, uint64_t pnt_time, fstHandle pnt_facidx, const unsigned char *pnt_value, uint32_t plen)
{
	FstData *ptr = (FstData*)user_data;
	ptr->reconstruct_edges_callback(pnt_time, pnt_facidx, pnt_value, plen);
}

static void reconstruct_edges(void *user_data, uint64_t pnt_time, fstHandle pnt_facidx, const unsigned char *pnt_value)
{
	FstData *ptr = (FstData*)user_data;
	uint32_t plen = (pnt_value) ?  strlen((const char *)pnt_value) : 0;
	ptr->reconstruct_edges_callback(pnt_time, pnt_facidx, pnt_value, plen);
}

void FstData::reconstruct_edges_callback(uint64_t pnt_time, fstHandle pnt_facidx, const unsigned char *pnt_value, uint32_t /* plen */)
{
	std::string val = std::string((const char *)pnt_value);
	std::string prev = last_data[pnt_facidx];
	if (pnt_time>=start_time) {
		if (prev!="1" && val=="1")
			edges.push_back(pnt_time);
		if (prev!="0" && val=="0")
			edges.push_back(pnt_time);
	}
	last_data[pnt_facidx] = val;
}

std::vector<uint64_t> FstData::getAllEdges(std::vector<fstHandle> &signal, uint64_t start, uint64_t end)
{
	start_time = start;
	end_time = end;
	last_data.clear();
	for(auto &s : signal) {
		last_data[s] = "x";
	}
	edges.clear();
	fstReaderSetLimitTimeRange(ctx, start_time, end_time);
	fstReaderClrFacProcessMaskAll(ctx);
	for(const auto sig : signal)
		fstReaderSetFacProcessMask(ctx,sig);
	fstReaderIterBlocks2(ctx, reconstruct_edges, reconstruct_edges_varlen, this, nullptr);
	return edges;
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
	if (sample_times_ndx >= sample_times.size()) return;

	uint64_t time = sample_times[sample_times_ndx];
	// if we are past the timestamp
	if (pnt_time > time) {
		for (auto const& c : last_data)
		{
			handle_to_data[c.first].push_back(std::make_pair(time,c.second));
			size_t index = handle_to_data[c.first].size() - 1;
			time_to_index[c.first][time] = index;
		}
		sample_times_ndx++;
	}
	// always update last_data
	last_data[pnt_facidx] =  std::string((const char *)pnt_value);
}

void FstData::reconstructAtTimes(std::vector<fstHandle> &signal, std::vector<uint64_t> time)
{
	handle_to_data.clear();
	time_to_index.clear();
	last_data.clear();
	sample_times_ndx = 0;
	sample_times = time;
	fstReaderSetUnlimitedTimeRange(ctx);
	fstReaderClrFacProcessMaskAll(ctx);
	for(const auto sig : signal)
		fstReaderSetFacProcessMask(ctx,sig);
	fstReaderIterBlocks2(ctx, reconstruct_clb_attimes, reconstruct_clb_varlen_attimes, this, nullptr);

	if (time_to_index[signal.back()].count(time.back())==0) {
		for (auto const& c : last_data)
		{
			handle_to_data[c.first].push_back(std::make_pair(time.back(),c.second));
			size_t index = handle_to_data[c.first].size() - 1;
			time_to_index[c.first][time.back()] = index;
		}
	}
}

void FstData::reconstructAllAtTimes(std::vector<uint64_t> time)
{
	handle_to_data.clear();
	time_to_index.clear();
	last_data.clear();
	sample_times_ndx = 0;
	sample_times = time;

	fstReaderSetUnlimitedTimeRange(ctx);
	fstReaderSetFacProcessMaskAll(ctx);
	fstReaderIterBlocks2(ctx, reconstruct_clb_attimes, reconstruct_clb_varlen_attimes, this, nullptr);

	if (time_to_index[1].count(time.back())==0) {
		for (auto const& c : last_data)
		{
			handle_to_data[c.first].push_back(std::make_pair(time.back(),c.second));
			size_t index = handle_to_data[c.first].size() - 1;
			time_to_index[c.first][time.back()] = index;
		}
	}
}

std::string FstData::valueAt(fstHandle signal, uint64_t time)
{
	if (handle_to_data.find(signal) == handle_to_data.end())
		log_error("Signal id %d not found\n", (int)signal);
	auto &data = handle_to_data[signal];
	if (time_to_index[signal].count(time)!=0) {
		size_t index = time_to_index[signal][time];
		return data.at(index).second;
	} else {
		log_error("No data for signal %d at time %d\n", (int)signal, (int)time);
	}
}
