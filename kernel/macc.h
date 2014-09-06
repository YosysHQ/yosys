/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Clifford Wolf <clifford@clifford.at>
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

#ifndef MACC_H
#define MACC_H

#include "kernel/yosys.h"

YOSYS_NAMESPACE_BEGIN

struct Macc
{
	struct port_t {
		RTLIL::SigSpec in_a, in_b;
		bool is_signed, do_subtract;
	};

	std::vector<port_t> ports;
	RTLIL::SigSpec bit_ports;

	void from_cell(RTLIL::Cell *cell)
	{
		RTLIL::SigSpec port_a = cell->getPort("\\A");

		ports.clear();
		bit_ports = cell->getPort("\\B");

		std::vector<RTLIL::State> config_bits = cell->getParam("\\CONFIG").bits;
		int config_width = cell->getParam("\\CONFIG_WIDTH").as_int();
		int config_cursor = 0;

		log_assert(SIZE(config_bits) >= config_width);

		int num_bits = 0;
		if (config_bits[config_cursor++] == RTLIL::S1) num_bits |= 1;
		if (config_bits[config_cursor++] == RTLIL::S1) num_bits |= 2;
		if (config_bits[config_cursor++] == RTLIL::S1) num_bits |= 4;
		if (config_bits[config_cursor++] == RTLIL::S1) num_bits |= 8;

		int port_a_cursor = 0;
		while (port_a_cursor < SIZE(port_a))
		{
			log_assert(config_cursor + 2 + 2*num_bits <= config_width);

			port_t this_port;
			this_port.is_signed = config_bits[config_cursor++] == RTLIL::S1;
			this_port.do_subtract = config_bits[config_cursor++] == RTLIL::S1;

			int size_a = 0;
			for (int i = 0; i < num_bits; i++)
				if (config_bits[config_cursor++] == RTLIL::S1)
					size_a |= 1 << i;

			this_port.in_a = port_a.extract(port_a_cursor, size_a);
			port_a_cursor += size_a;

			int size_b = 0;
			for (int i = 0; i < num_bits; i++)
				if (config_bits[config_cursor++] == RTLIL::S1)
					size_b |= 1 << i;

			this_port.in_b = port_a.extract(port_a_cursor, size_b);
			port_a_cursor += size_b;

			if (size_a || size_b)
				ports.push_back(this_port);
		}

		log_assert(config_cursor == config_width);
		log_assert(port_a_cursor == SIZE(port_a));
	}

	void to_cell(RTLIL::Cell *cell) const
	{
		RTLIL::SigSpec port_a;
		std::vector<RTLIL::State> config_bits;
		int max_size = 0, num_bits = 0;

		for (auto &port : ports) {
			max_size = std::max(max_size, SIZE(port.in_a));
			max_size = std::max(max_size, SIZE(port.in_b));
		}

		while (max_size)
			num_bits++, max_size /= 2;

		log_assert(num_bits < 16);
		config_bits.push_back(num_bits & 1 ? RTLIL::S1 : RTLIL::S0);
		config_bits.push_back(num_bits & 2 ? RTLIL::S1 : RTLIL::S0);
		config_bits.push_back(num_bits & 4 ? RTLIL::S1 : RTLIL::S0);
		config_bits.push_back(num_bits & 8 ? RTLIL::S1 : RTLIL::S0);

		for (auto &port : ports)
		{
			if (SIZE(port.in_a) == 0)
				continue;

			config_bits.push_back(port.is_signed ? RTLIL::S1 : RTLIL::S0);
			config_bits.push_back(port.do_subtract ? RTLIL::S1 : RTLIL::S0);

			int size_a = SIZE(port.in_a);
			for (int i = 0; i < num_bits; i++)
				config_bits.push_back(size_a & (1 << i) ? RTLIL::S1 : RTLIL::S0);

			int size_b = SIZE(port.in_b);
			for (int i = 0; i < num_bits; i++)
				config_bits.push_back(size_b & (1 << i) ? RTLIL::S1 : RTLIL::S0);

			port_a.append(port.in_a);
			port_a.append(port.in_b);
		}

		cell->setPort("\\A", port_a);
		cell->setPort("\\B", bit_ports);
		cell->setParam("\\CONFIG", config_bits);
		cell->setParam("\\CONFIG_WIDTH", SIZE(config_bits));
		cell->setParam("\\A_WIDTH", SIZE(port_a));
		cell->setParam("\\B_WIDTH", SIZE(bit_ports));
	}

	bool eval(RTLIL::Const &result) const
	{
		for (auto &bit : result.bits)
			bit = RTLIL::S0;

		for (auto &port : ports)
		{
			if (!port.in_a.is_fully_const() || !port.in_b.is_fully_const())
				return false;

			RTLIL::Const summand;
			if (SIZE(port.in_b) == 0)
				summand = const_pos(port.in_a.as_const(), port.in_b.as_const(), port.is_signed, port.is_signed, SIZE(result));
			else
				summand = const_mul(port.in_a.as_const(), port.in_b.as_const(), port.is_signed, port.is_signed, SIZE(result));

			if (port.do_subtract)
				result = const_sub(result, summand, port.is_signed, port.is_signed, SIZE(result));
			else
				result = const_add(result, summand, port.is_signed, port.is_signed, SIZE(result));
		}

		for (auto bit : bit_ports) {
			if (bit.wire)
				return false;
			result = const_add(result, bit.data, false, false, SIZE(result));
		}

		return true;
	}
};

YOSYS_NAMESPACE_END

#endif
