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
	ctx = (fstReaderContext *)fstReaderOpen(filename.c_str());
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
		log("Not found key %s\n", name.c_str());
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
				//log("adding %s.%s\n",var.scope.c_str(), clean_name.c_str());
				
				name_to_handle[var.scope+"."+clean_name] = h->u.var.handle;
				break;
			}
		}
	}
}

static void reconstruct_clb_varlen(void *user_data, uint64_t pnt_time, fstHandle pnt_facidx, const unsigned char *pnt_value, uint32_t plen)
{
	FstData *ptr = (FstData*)user_data;
	ptr->reconstruct_callback(pnt_time, pnt_facidx, pnt_value, plen);
}

static void reconstruct_clb(void *user_data, uint64_t pnt_time, fstHandle pnt_facidx, const unsigned char *pnt_value)
{
	FstData *ptr = (FstData*)user_data;
	uint32_t plen = (pnt_value) ?  strlen((const char *)pnt_value) : 0;
	ptr->reconstruct_callback(pnt_time, pnt_facidx, pnt_value, plen);
}

void FstData::reconstruct_callback(uint64_t pnt_time, fstHandle pnt_facidx, const unsigned char *pnt_value, uint32_t /* plen */)
{
	handle_to_data[pnt_facidx].push_back(std::make_pair(pnt_time, std::string((const char *)pnt_value)));
	size_t index = handle_to_data[pnt_facidx].size() - 1;
	time_to_index[pnt_facidx][pnt_time] = index;
	index_to_time[pnt_facidx][index] = pnt_time;
}

void FstData::reconstruct(std::vector<fstHandle> &signal)
{
	handle_to_data.clear();
	time_to_index.clear();
	index_to_time.clear();
	fstReaderClrFacProcessMaskAll(ctx);
	for(const auto sig : signal)
		fstReaderSetFacProcessMask(ctx,sig);
	fstReaderIterBlocks2(ctx, reconstruct_clb, reconstruct_clb_varlen, this, nullptr);
}

void FstData::reconstuctAll()
{
	handle_to_data.clear();
	time_to_index.clear();
	index_to_time.clear();
	fstReaderSetFacProcessMaskAll(ctx);
	fstReaderIterBlocks2(ctx, reconstruct_clb, reconstruct_clb_varlen, this, nullptr);
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
	if (sample_times_ndx > sample_times.size()) return;
	uint64_t time = sample_times[sample_times_ndx];
	// if we are past the timestamp
	if (pnt_time > time) {
		for (auto const& c : current)
		{
			handle_to_data[c.first].push_back(std::make_pair(time,c.second));
			size_t index = handle_to_data[c.first].size() - 1;
			time_to_index[c.first][time] = index;
			index_to_time[c.first][index] = time;
		}
		sample_times_ndx++;
	}
	// always update current
	current[pnt_facidx] =  std::string((const char *)pnt_value);
}

void FstData::reconstructAtTimes(std::vector<fstHandle> &signal, std::vector<uint64_t> time)
{
	handle_to_data.clear();
	time_to_index.clear();
	index_to_time.clear();
	current.clear();
	sample_times_ndx = 0;
	sample_times = time;
	fstReaderClrFacProcessMaskAll(ctx);
	for(const auto sig : signal)
		fstReaderSetFacProcessMask(ctx,sig);
	fstReaderIterBlocks2(ctx, reconstruct_clb_attimes, reconstruct_clb_varlen_attimes, this, nullptr);

	if (time_to_index[signal.back()].count(time.back())==0) {
		for (auto const& c : current)
		{
			handle_to_data[c.first].push_back(std::make_pair(time.back(),c.second));
			size_t index = handle_to_data[c.first].size() - 1;
			time_to_index[c.first][time.back()] = index;
			index_to_time[c.first][index] = time.back();
		}
	}
}

void FstData::reconstructAllAtTimes(std::vector<uint64_t> time)
{
	handle_to_data.clear();
	time_to_index.clear();
	index_to_time.clear();
	current.clear();
	sample_times_ndx = 0;
	sample_times = time;
	fstReaderSetFacProcessMaskAll(ctx);
	fstReaderIterBlocks2(ctx, reconstruct_clb_attimes, reconstruct_clb_varlen_attimes, this, nullptr);
/*
	if (time_to_index[signal.back()].count(time.back())==0) {
		for (auto const& c : current)
		{
			handle_to_data[c.first].push_back(std::make_pair(time.back(),c.second));
			size_t index = handle_to_data[c.first].size() - 1;
			time_to_index[c.first][time.back()] = index;
			index_to_time[c.first][index] = time.back();
		}
	}*/
}

std::string FstData::valueAt(fstHandle signal, uint64_t time)
{
	// TODO: Check if signal exist
	auto &data = handle_to_data[signal];
	if (time_to_index[signal].count(time)!=0) {
		size_t index = time_to_index[signal][time];
		return data.at(index).second;
	} else {
		size_t index = 0;
		for(size_t i = 0; i< data.size(); i++) {
			uint64_t t = index_to_time[signal][i];
			if (t > time) 
				break;
			index = i;
		}
		return data.at(index).second;
	}
}

std::vector<uint64_t> FstData::edges(fstHandle signal, bool positive, bool negative)
{
	// TODO: Check if signal exist
	auto &data = handle_to_data[signal];
	std::string prev = "x";
	std::vector<uint64_t> retVal;
	for(auto &d : data) {
		if (positive && prev=="0" && d.second=="1")
			retVal.push_back(d.first);
		if (negative && prev=="1" && d.second=="0")
			retVal.push_back(d.first);
		prev = d.second;
	}
	return retVal;
}

void FstData::recalc_time_offsets(fstHandle signal, std::vector<uint64_t> time)
{
	size_t index = 0;
	auto &data = handle_to_data[signal];
	for(auto curr : time) {
		for(size_t i = index; i< data.size(); i++) {
			uint64_t t = index_to_time[signal][i];
			if (t > curr) 
				break;
			index = i;
		}
		time_to_index[signal][curr] = index;
	}
}
