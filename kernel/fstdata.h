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

#ifndef FSTDATA_H
#define FSTDATA_H

#include "kernel/yosys.h"
#include "libs/fst/fstapi.h"

YOSYS_NAMESPACE_BEGIN

struct FstVar
{
	fstHandle id;
	std::string name;
	bool is_alias;
	std::string scope;
	int width;
};

class FstData
{
	public:
	FstData(std::string filename);
	~FstData();

	uint64_t getStartTime();
	uint64_t getEndTime();

	std::vector<FstVar>& getVars() { return vars; };

	void reconstruct_edges_callback(uint64_t pnt_time, fstHandle pnt_facidx, const unsigned char *pnt_value, uint32_t plen);
	std::vector<uint64_t> getAllEdges(std::vector<fstHandle> &signal, uint64_t start_time, uint64_t end_time);

	void reconstruct_callback_attimes(uint64_t pnt_time, fstHandle pnt_facidx, const unsigned char *pnt_value, uint32_t plen);
	void reconstructAtTimes(std::vector<fstHandle> &signal,std::vector<uint64_t> time);
	void reconstructAllAtTimes(std::vector<uint64_t> time);

	std::string valueAt(fstHandle signal, uint64_t time);
	fstHandle getHandle(std::string name);
	double getTimescale() { return timescale; }
	const char *getTimescaleString() { return timescale_str.c_str(); }
private:
	void extractVarNames();

	struct fstReaderContext *ctx;
	std::vector<std::string> scopes;
	std::vector<FstVar> vars;
	std::map<fstHandle, FstVar> handle_to_var;
	std::map<std::string, fstHandle> name_to_handle;
	std::map<fstHandle, std::vector<std::pair<uint64_t, std::string>>> handle_to_data;
	std::map<fstHandle, std::string> last_data;
	std::map<fstHandle, std::map<uint64_t, size_t>> time_to_index;
	std::vector<uint64_t> sample_times;
	size_t sample_times_ndx;
	double timescale;
	std::string timescale_str;
	uint64_t start_time;
	uint64_t end_time;
	std::vector<uint64_t> edges;
};

YOSYS_NAMESPACE_END

#endif
