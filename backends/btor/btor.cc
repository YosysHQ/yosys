/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Clifford Wolf <clifford@clifford.at>
 *  Copyright (C) 2014  Ahmed Irfan <irfan@fbk.eu>
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

// [[CITE]] BTOR: Bit-Precise Modelling of Word-Level Problems for Model Checking
// Johannes Kepler University, Linz, Austria
// http://fmv.jku.at/papers/BrummayerBiereLonsing-BPR08.pdf

#include "kernel/rtlil.h"
#include "kernel/register.h"
#include "kernel/sigtools.h"
#include "kernel/celltypes.h"
#include "kernel/log.h"
#include <string>
#include <math.h>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct BtorDumperConfig
{
	bool subckt_mode;
	bool conn_mode;
	bool impltf_mode;

	std::string buf_type, buf_in, buf_out;
	std::string true_type, true_out, false_type, false_out;

	BtorDumperConfig() : subckt_mode(false), conn_mode(false), impltf_mode(false) { }
};

struct WireInfo
{
	RTLIL::IdString cell_name;
	const RTLIL::SigChunk *chunk;

	WireInfo(RTLIL::IdString c, const RTLIL::SigChunk* ch) : cell_name(c), chunk(ch) { }
};

struct WireInfoOrder
{
	bool operator() (const WireInfo& x, const WireInfo& y)
	{
		return x.chunk < y.chunk;
	}
};

struct BtorDumper
{
	std::ostream &f;
	RTLIL::Module *module;
	RTLIL::Design *design;
	BtorDumperConfig *config;
	CellTypes ct;

	SigMap sigmap;
	std::map<RTLIL::IdString, std::set<WireInfo,WireInfoOrder>> inter_wire_map;//<wire, dependency list> for mapping the intermediate wires that are output of some cell
	std::map<RTLIL::IdString, int> line_ref;//mapping of ids to line_num of the btor file
	std::map<RTLIL::SigSpec, int> sig_ref;//mapping of sigspec to the line_num of the btor file
	int line_num;//last line number of btor file
	std::string str;//temp string for writing file
	std::map<RTLIL::IdString, bool> basic_wires;//input wires and registers
	RTLIL::IdString curr_cell; //current cell being dumped
	std::map<std::string, std::string> cell_type_translation, s_cell_type_translation; //RTLIL to BTOR translation
        std::map<int, std::set<std::pair<int,int>>> mem_next; // memory (line_number)'s set of condition and write
	BtorDumper(std::ostream &f, RTLIL::Module *module, RTLIL::Design *design, BtorDumperConfig *config) :
		f(f), module(module), design(design), config(config), ct(design), sigmap(module)
	{
		line_num=0;
		str.clear();
		for(auto it=module->wires_.begin(); it!=module->wires_.end(); ++it)
		{
			if(it->second->port_input)
			{
				basic_wires[it->first]=true;
			}
			else
			{
				basic_wires[it->first]=false;
			}
			inter_wire_map[it->first].clear();
		}
		curr_cell.clear();
		//assert
		cell_type_translation["$assert"] = "root";
		//unary
		cell_type_translation["$not"] = "not";
		cell_type_translation["$neg"] = "neg";
		cell_type_translation["$reduce_and"] = "redand";
		cell_type_translation["$reduce_or"] = "redor";
		cell_type_translation["$reduce_xor"] = "redxor";
		cell_type_translation["$reduce_bool"] = "redor";
		//binary
		cell_type_translation["$and"] = "and";
		cell_type_translation["$or"] = "or";
		cell_type_translation["$xor"] = "xor";
		cell_type_translation["$xnor"] = "xnor";
		cell_type_translation["$shr"] = "srl";
		cell_type_translation["$shl"] = "sll";
		cell_type_translation["$sshr"] = "sra";
		cell_type_translation["$sshl"] = "sll";
		cell_type_translation["$shift"] = "srl";
		cell_type_translation["$shiftx"] = "srl";
		cell_type_translation["$lt"] = "ult";
		cell_type_translation["$le"] = "ulte";
		cell_type_translation["$gt"] = "ugt";
		cell_type_translation["$ge"] = "ugte";
		cell_type_translation["$eq"] = "eq";
		cell_type_translation["$eqx"] = "eq";
		cell_type_translation["$ne"] = "ne";
		cell_type_translation["$nex"] = "ne";
		cell_type_translation["$add"] = "add";
		cell_type_translation["$sub"] = "sub";
		cell_type_translation["$mul"] = "mul";
		cell_type_translation["$mod"] = "urem";
		cell_type_translation["$div"] = "udiv";
		//mux
		cell_type_translation["$mux"] = "cond";
		//reg
		cell_type_translation["$dff"] = "next";
		cell_type_translation["$adff"] = "next";
		cell_type_translation["$dffsr"] = "next";
		//memories
		//nothing here
		//slice
		cell_type_translation["$slice"] = "slice";
		//concat
		cell_type_translation["$concat"] = "concat";

		//signed cell type translation
		//binary
		s_cell_type_translation["$modx"] = "srem";
		s_cell_type_translation["$mody"] = "smod";
		s_cell_type_translation["$div"] = "sdiv";
		s_cell_type_translation["$lt"] = "slt";
		s_cell_type_translation["$le"] = "slte";
		s_cell_type_translation["$gt"] = "sgt";
		s_cell_type_translation["$ge"] = "sgte";

	}

	vector<shared_str> cstr_buf;

	const char *cstr(const RTLIL::IdString id)
	{
		str = RTLIL::unescape_id(id);
		for (size_t i = 0; i < str.size(); ++i)
			if (str[i] == '#' || str[i] == '=')
				str[i] = '?';
		cstr_buf.push_back(str);
		return cstr_buf.back().c_str();
	}

	int dump_wire(RTLIL::Wire* wire)
	{
		if(basic_wires[wire->name])
		{
			log("writing wire %s\n", cstr(wire->name));
			auto it = line_ref.find(wire->name);
			if(it==std::end(line_ref))
			{
				++line_num;
				line_ref[wire->name]=line_num;
				str = stringf("%d var %d %s", line_num, wire->width, cstr(wire->name));
				f << stringf("%s\n", str.c_str());
				return line_num;
			}
			else return it->second;
		}
		else // case when the wire is not basic wire
		{
			log("case of non-basic wire - %s\n", cstr(wire->name));
			auto it = line_ref.find(wire->name);
			if(it==std::end(line_ref))
			{
				std::set<WireInfo, WireInfoOrder>& dep_set = inter_wire_map.at(wire->name);
				int wire_line = 0;
				int wire_width = 0;
				for(auto dep_set_it=dep_set.begin(); dep_set_it!=dep_set.end(); ++dep_set_it)
				{
					RTLIL::IdString cell_id = dep_set_it->cell_name;
					if(cell_id == curr_cell)
						break;
					log(" -- found cell %s\n", cstr(cell_id));
					RTLIL::Cell* cell = module->cells_.at(cell_id);
					const RTLIL::SigSpec* cell_output = get_cell_output(cell);
					int cell_line = dump_cell(cell);

					if(dep_set.size()==1 && wire->width == cell_output->size())
					{
						wire_line = cell_line;
						break;
					}
					else
					{
						int prev_wire_line=0; //previously dumped wire line
						int start_bit=0;
						for(unsigned j=0; j<cell_output->chunks().size(); ++j)
						{
							start_bit+=cell_output->chunks().at(j).width;
							if(cell_output->chunks().at(j).wire->name == wire->name)
							{
								prev_wire_line = wire_line;
								wire_line = ++line_num;
								str = stringf("%d slice %d %d %d %d;1", line_num, cell_output->chunks().at(j).width,
									cell_line, start_bit-1, start_bit-cell_output->chunks().at(j).width);
								f << stringf("%s\n", str.c_str());
								wire_width += cell_output->chunks().at(j).width;
								if(prev_wire_line!=0)
								{
									++line_num;
									str = stringf("%d concat %d %d %d", line_num, wire_width, wire_line, prev_wire_line);
									f << stringf("%s\n", str.c_str());
									wire_line = line_num;
								}
							}
						}
					}
				}
				if(dep_set.size()==0)
				{
					log(" - checking sigmap\n");
					RTLIL::SigSpec s = RTLIL::SigSpec(wire);
					wire_line = dump_sigspec(&s, s.size());
					line_ref[wire->name]=wire_line;
				}
				line_ref[wire->name]=wire_line;
				return wire_line;
			}
			else
			{
				log(" -- already processed wire\n");
				return it->second;
			}
		}
		log_abort();
		return -1;
	}

	int dump_memory(const RTLIL::Memory* memory)
	{
		log("writing memory %s\n", cstr(memory->name));
		auto it = line_ref.find(memory->name);
		if(it==std::end(line_ref))
		{
			++line_num;
			int address_bits = ceil_log2(memory->size);
			str = stringf("%d array %d %d", line_num, memory->width, address_bits);
			line_ref[memory->name]=line_num;
			f << stringf("%s\n", str.c_str());
			return line_num;
		}
		else return it->second;
	}

        int dump_memory_next(const RTLIL::Memory* memory)
        {
	  auto mem_it = line_ref.find(memory->name);
	  int address_bits = ceil_log2(memory->size);
	  if(mem_it==std::end(line_ref))
	    {
	      log("can not write next of a memory that is not dumped yet\n");
	      log_abort();
	    }
	  else
	    {
	      auto acond_list_it = mem_next.find(mem_it->second);
	      if(acond_list_it!=std::end(mem_next))
		{
		  std::set<std::pair<int,int>>& cond_list = acond_list_it->second;
		  if(cond_list.empty())
		    {
		      return 0;
		    }
		  auto it=cond_list.begin();
		  ++line_num;
		  str = stringf("%d acond %d %d %d %d %d", line_num, memory->width, address_bits, it->first, it->second, mem_it->second);
		  f << stringf("%s\n", str.c_str());
		  ++it;
		  for(; it!=cond_list.end(); ++it)
		    {
		      ++line_num;
		      str = stringf("%d acond %d %d %d %d %d", line_num, memory->width, address_bits, it->first, it->second, line_num-1);
		      f << stringf("%s\n", str.c_str());
		    }
		  ++line_num;
		  str = stringf("%d anext %d %d %d %d", line_num, memory->width, address_bits, mem_it->second, line_num-1);
		  f << stringf("%s\n", str.c_str());
		  return 1;
		}
	      return 0;
	    }
	}

	int dump_const(const RTLIL::Const* data, int width, int offset)
	{
		log("writing const \n");
		if((data->flags & RTLIL::CONST_FLAG_STRING) == 0)
		{
			if(width<0)
				width = data->bits.size() - offset;

			std::string data_str = data->as_string();
			//if(offset > 0)
				data_str = data_str.substr(offset, width);

			++line_num;
			str = stringf("%d const %d %s", line_num, width, data_str.c_str());
			f << stringf("%s\n", str.c_str());
			return line_num;
		}
		else
			log("writing const error\n");
		log_abort();
		return -1;
	}

	int dump_sigchunk(const RTLIL::SigChunk* chunk)
	{
		log("writing sigchunk\n");
		int l=-1;
		if(chunk->wire == NULL)
		{
			RTLIL::Const data_const(chunk->data);
			l=dump_const(&data_const, chunk->width, chunk->offset);
		}
		else
		{
			if (chunk->width == chunk->wire->width && chunk->offset == 0)
				l = dump_wire(chunk->wire);
			else
			{
				int wire_line_num = dump_wire(chunk->wire);
				log_assert(wire_line_num>0);
				++line_num;
				str = stringf("%d slice %d %d %d %d;2", line_num, chunk->width, wire_line_num,
					chunk->width + chunk->offset - 1, chunk->offset);
				f << stringf("%s\n", str.c_str());
				l = line_num;
			}
		}
		return l;
	}

	int dump_sigspec(const RTLIL::SigSpec* sig, int expected_width)
	{
		log("writing sigspec\n");
		RTLIL::SigSpec s = sigmap(*sig);
		int l = -1;
		auto it = sig_ref.find(s);
		if(it == std::end(sig_ref))
		{
			if (s.is_chunk())
			{
				l = dump_sigchunk(&s.chunks().front());
			}
			else
			{
				int l1, l2, w1, w2;
				l1 = dump_sigchunk(&s.chunks().front());
				log_assert(l1>0);
				w1 = s.chunks().front().width;
				for (unsigned i=1; i < s.chunks().size(); ++i)
				{
					l2 = dump_sigchunk(&s.chunks().at(i));
					log_assert(l2>0);
					w2 = s.chunks().at(i).width;
					++line_num;
					str = stringf("%d concat %d %d %d", line_num, w1+w2, l2, l1);
					f << stringf("%s\n", str.c_str());
					l1=line_num;
					w1+=w2;
				}
				l = line_num;
			}
			sig_ref[s] = l;
		}
		else
		{
			l = it->second;
		}

		if (expected_width != s.size())
		{
			log(" - changing width of sigspec\n");
			//TODO: this block may not be needed anymore, due to explicit type conversion by "splice" command
			if(expected_width > s.size())
			{
				//TODO: case the signal is signed
				++line_num;
				str = stringf ("%d zero %d", line_num, expected_width - s.size());
				f << stringf("%s\n", str.c_str());
				++line_num;
				str = stringf ("%d concat %d %d %d", line_num, expected_width, line_num-1, l);
				f << stringf("%s\n", str.c_str());
				l = line_num;
			}
			else if(expected_width < s.size())
			{
				++line_num;
				str = stringf ("%d slice %d %d %d %d;3", line_num, expected_width, l, expected_width-1, 0);
				f << stringf("%s\n", str.c_str());
				l = line_num;
			}
		}
		log_assert(l>0);
		return l;
	}

	int dump_cell(const RTLIL::Cell* cell)
	{
		auto it = line_ref.find(cell->name);
		if(it==std::end(line_ref))
		{
			curr_cell = cell->name;
			//assert cell
			if(cell->type == "$assert")
			{
				log("writing assert cell - %s\n", cstr(cell->type));
				const RTLIL::SigSpec* expr = &cell->getPort(RTLIL::IdString("\\A"));
				const RTLIL::SigSpec* en = &cell->getPort(RTLIL::IdString("\\EN"));
				log_assert(expr->size() == 1);
				log_assert(en->size() == 1);
				int expr_line = dump_sigspec(expr, 1);
				int en_line = dump_sigspec(en, 1);
				int one_line = ++line_num;
				str = stringf("%d one 1", line_num);
				f << stringf("%s\n", str.c_str());
				++line_num;
				str = stringf("%d %s %d %d %d", line_num, cell_type_translation.at("$eq").c_str(), 1, en_line, one_line);
				f << stringf("%s\n", str.c_str());
				++line_num;
				str = stringf("%d %s %d %d %d %d", line_num, cell_type_translation.at("$mux").c_str(), 1, line_num-1,
					expr_line, one_line);
				f << stringf("%s\n", str.c_str());
				int cell_line = ++line_num;
				str = stringf("%d %s %d %d", line_num, cell_type_translation.at("$assert").c_str(), 1, -1*(line_num-1));
				//multiplying the line number with -1, which means logical negation
				//the reason for negative sign is that the properties in btor are given as "negation of the original property"
				//bug identified by bobosoft
				//http://www.reddit.com/r/yosys/comments/1w3xig/btor_backend_bug/
				f << stringf("%s\n", str.c_str());
				line_ref[cell->name]=cell_line;
			}
			//unary cells
			else if(cell->type == "$not" || cell->type == "$neg" || cell->type == "$pos" || cell->type == "$reduce_and" ||
				cell->type == "$reduce_or" || cell->type == "$reduce_xor" || cell->type == "$reduce_bool")
			{
				log("writing unary cell - %s\n", cstr(cell->type));
				int w = cell->parameters.at(RTLIL::IdString("\\A_WIDTH")).as_int();
				int output_width = cell->parameters.at(RTLIL::IdString("\\Y_WIDTH")).as_int();
				w = w>output_width ? w:output_width; //padding of w
				int l = dump_sigspec(&cell->getPort(RTLIL::IdString("\\A")), w);
				int cell_line = l;
				if(cell->type != "$pos")
				{
					cell_line = ++line_num;
					bool reduced = (cell->type == "$not" || cell->type == "$neg") ? false : true;
					str = stringf ("%d %s %d %d", cell_line, cell_type_translation.at(cell->type.str()).c_str(), reduced?output_width:w, l);
					f << stringf("%s\n", str.c_str());
				}
				if(output_width < w && (cell->type == "$not" || cell->type == "$neg" || cell->type == "$pos"))
				{
					++line_num;
					str = stringf ("%d slice %d %d %d %d;4", line_num, output_width, cell_line, output_width-1, 0);
					f << stringf("%s\n", str.c_str());
					cell_line = line_num;
				}
				line_ref[cell->name]=cell_line;
			}
			else if(cell->type == "$reduce_xnor" || cell->type == "$logic_not")//no direct translation in btor
			{
				log("writing unary cell - %s\n", cstr(cell->type));
				int w = cell->parameters.at(RTLIL::IdString("\\A_WIDTH")).as_int();
				int output_width = cell->parameters.at(RTLIL::IdString("\\Y_WIDTH")).as_int();
				log_assert(output_width == 1);
				int l = dump_sigspec(&cell->getPort(RTLIL::IdString("\\A")), w);
				if(cell->type == "$logic_not" && w > 1)
				{
					++line_num;
					str = stringf ("%d %s %d %d", line_num, cell_type_translation.at("$reduce_or").c_str(), output_width, l);
					f << stringf("%s\n", str.c_str());
				}
				else if(cell->type == "$reduce_xnor")
				{
					++line_num;
					str = stringf ("%d %s %d %d", line_num, cell_type_translation.at("$reduce_xor").c_str(), output_width, l);
					f << stringf("%s\n", str.c_str());
				}
				++line_num;
				str = stringf ("%d %s %d %d", line_num, cell_type_translation.at("$not").c_str(), output_width, l);
				f << stringf("%s\n", str.c_str());
				line_ref[cell->name]=line_num;
			}
			//binary cells
			else if(cell->type == "$and" || cell->type == "$or" || cell->type == "$xor" || cell->type == "$xnor" ||
				 cell->type == "$lt" || cell->type == "$le" || cell->type == "$eq" || cell->type == "$ne" ||
				 cell->type == "$eqx" || cell->type == "$nex" || cell->type == "$ge" || cell->type == "$gt" )
			{
				log("writing binary cell - %s\n", cstr(cell->type));
				int output_width = cell->parameters.at(RTLIL::IdString("\\Y_WIDTH")).as_int();
				log_assert(!(cell->type == "$eq" || cell->type == "$ne" || cell->type == "$eqx" || cell->type == "$nex" ||
					cell->type == "$ge" || cell->type == "$gt") || output_width == 1);
				bool l1_signed = cell->parameters.at(RTLIL::IdString("\\A_SIGNED")).as_bool();
				bool l2_signed YS_ATTRIBUTE(unused) = cell->parameters.at(RTLIL::IdString("\\B_SIGNED")).as_bool();
				int l1_width = cell->parameters.at(RTLIL::IdString("\\A_WIDTH")).as_int();
				int l2_width = cell->parameters.at(RTLIL::IdString("\\B_WIDTH")).as_int();

				log_assert(l1_signed == l2_signed);
				l1_width = l1_width > output_width ? l1_width : output_width;
				l1_width = l1_width > l2_width ? l1_width : l2_width;
				l2_width = l2_width > l1_width ? l2_width : l1_width;

				int l1 = dump_sigspec(&cell->getPort(RTLIL::IdString("\\A")), l1_width);
				int l2 = dump_sigspec(&cell->getPort(RTLIL::IdString("\\B")), l2_width);

				++line_num;
				std::string op = cell_type_translation.at(cell->type.str());
				if(cell->type == "$lt" || cell->type == "$le" ||
				 cell->type == "$eq" || cell->type == "$ne" || cell->type == "$eqx" || cell->type == "$nex" ||
				 cell->type == "$ge" || cell->type == "$gt")
				{
					if(l1_signed)
						op = s_cell_type_translation.at(cell->type.str());
				}

				str = stringf ("%d %s %d %d %d", line_num, op.c_str(), output_width, l1, l2);
				f << stringf("%s\n", str.c_str());

				line_ref[cell->name]=line_num;
			}
			else if(cell->type == "$add" || cell->type == "$sub" || cell->type == "$mul" || cell->type == "$div" ||
				 cell->type == "$mod" )
			{
				//TODO: division by zero case
				log("writing binary cell - %s\n", cstr(cell->type));
				int output_width = cell->parameters.at(RTLIL::IdString("\\Y_WIDTH")).as_int();
				bool l1_signed = cell->parameters.at(RTLIL::IdString("\\A_SIGNED")).as_bool();
				bool l2_signed = cell->parameters.at(RTLIL::IdString("\\B_SIGNED")).as_bool();
				int l1_width = cell->parameters.at(RTLIL::IdString("\\A_WIDTH")).as_int();
				int l2_width = cell->parameters.at(RTLIL::IdString("\\B_WIDTH")).as_int();

				log_assert(l1_signed == l2_signed);
				l1_width = l1_width > output_width ? l1_width : output_width;
				l1_width = l1_width > l2_width ? l1_width : l2_width;
				l2_width = l2_width > l1_width ? l2_width : l1_width;

				int l1 = dump_sigspec(&cell->getPort(RTLIL::IdString("\\A")), l1_width);
				int l2 = dump_sigspec(&cell->getPort(RTLIL::IdString("\\B")), l2_width);

				++line_num;
				std::string op = cell_type_translation.at(cell->type.str());
				if(cell->type == "$div" && l1_signed)
					op = s_cell_type_translation.at(cell->type.str());
				else if(cell->type == "$mod")
				{
					if(l1_signed)
						op = s_cell_type_translation.at("$modx");
					else if(l2_signed)
						op = s_cell_type_translation.at("$mody");
				}
				str = stringf ("%d %s %d %d %d", line_num, op.c_str(), l1_width, l1, l2);
				f << stringf("%s\n", str.c_str());

				if(output_width < l1_width)
				{
					++line_num;
					str = stringf ("%d slice %d %d %d %d;5", line_num, output_width, line_num-1, output_width-1, 0);
					f << stringf("%s\n", str.c_str());
				}
				line_ref[cell->name]=line_num;
			}
			else if(cell->type == "$shr" || cell->type == "$shl" || cell->type == "$sshr" || cell->type == "$sshl" || cell->type == "$shift" || cell->type == "$shiftx")
			{
				log("writing binary cell - %s\n", cstr(cell->type));
				int output_width = cell->parameters.at(RTLIL::IdString("\\Y_WIDTH")).as_int();
				bool l1_signed = cell->parameters.at(RTLIL::IdString("\\A_SIGNED")).as_bool();
				//bool l2_signed = cell->parameters.at(RTLIL::IdString("\\B_SIGNED")).as_bool();
				int l1_width = cell->parameters.at(RTLIL::IdString("\\A_WIDTH")).as_int();
				l1_width = 1 << ceil_log2(l1_width);
				int l2_width = cell->parameters.at(RTLIL::IdString("\\B_WIDTH")).as_int();
				//log_assert(l2_width <= ceil_log2(l1_width)) );
				int l1 = dump_sigspec(&cell->getPort(RTLIL::IdString("\\A")), l1_width);
				int l2 = dump_sigspec(&cell->getPort(RTLIL::IdString("\\B")), ceil_log2(l1_width));
				int cell_output = ++line_num;
				str = stringf ("%d %s %d %d %d", line_num, cell_type_translation.at(cell->type.str()).c_str(), l1_width, l1, l2);
				f << stringf("%s\n", str.c_str());

				if(l2_width > ceil_log2(l1_width))
				{
					int extra_width = l2_width - ceil_log2(l1_width);
					l2 = dump_sigspec(&cell->getPort(RTLIL::IdString("\\B")), l2_width);
					++line_num;
					str = stringf ("%d slice %d %d %d %d;6", line_num, extra_width, l2, l2_width-1, l2_width-extra_width);
					f << stringf("%s\n", str.c_str());
					++line_num;
					str = stringf ("%d one %d", line_num, extra_width);
					f << stringf("%s\n", str.c_str());
					int mux = ++line_num;
					str = stringf ("%d %s %d %d %d", line_num, cell_type_translation.at("$gt").c_str(), 1, line_num-2, line_num-1);
					f << stringf("%s\n", str.c_str());
					++line_num;
					str = stringf("%d %s %d", line_num, l1_signed && cell->type == "$sshr" ? "ones":"zero", l1_width);
					f << stringf("%s\n", str.c_str());
					++line_num;
					str = stringf ("%d %s %d %d %d %d", line_num, cell_type_translation.at("$mux").c_str(), l1_width, mux, line_num-1, cell_output);
					f << stringf("%s\n", str.c_str());
					cell_output = line_num;
				}

				if(output_width < l1_width)
				{
					++line_num;
					str = stringf ("%d slice %d %d %d %d;5", line_num, output_width, cell_output, output_width-1, 0);
					f << stringf("%s\n", str.c_str());
					cell_output = line_num;
				}
				line_ref[cell->name] = cell_output;
			}
			else if(cell->type == "$logic_and" || cell->type == "$logic_or")//no direct translation in btor
			{
				log("writing binary cell - %s\n", cstr(cell->type));
				int output_width = cell->parameters.at(RTLIL::IdString("\\Y_WIDTH")).as_int();
				log_assert(output_width == 1);
				int l1 = dump_sigspec(&cell->getPort(RTLIL::IdString("\\A")), output_width);
				int l2 = dump_sigspec(&cell->getPort(RTLIL::IdString("\\B")), output_width);
				int l1_width = cell->parameters.at(RTLIL::IdString("\\A_WIDTH")).as_int();
				int l2_width = cell->parameters.at(RTLIL::IdString("\\B_WIDTH")).as_int();
				if(l1_width >1)
				{
					++line_num;
					str = stringf ("%d %s %d %d", line_num, cell_type_translation.at("$reduce_or").c_str(), output_width, l1);
					f << stringf("%s\n", str.c_str());
					l1 = line_num;
				}
				if(l2_width > 1)
				{
					++line_num;
					str = stringf ("%d %s %d %d", line_num, cell_type_translation.at("$reduce_or").c_str(), output_width, l2);
					f << stringf("%s\n", str.c_str());
					l2 = line_num;
				}
				if(cell->type == "$logic_and")
				{
					++line_num;
					str = stringf ("%d %s %d %d %d", line_num, cell_type_translation.at("$and").c_str(), output_width, l1, l2);
				}
				else if(cell->type == "$logic_or")
				{
					++line_num;
					str = stringf ("%d %s %d %d %d", line_num, cell_type_translation.at("$or").c_str(), output_width, l1, l2);
				}
				f << stringf("%s\n", str.c_str());
				line_ref[cell->name]=line_num;
			}
			//multiplexers
			else if(cell->type == "$mux")
			{
				log("writing mux cell\n");
				int output_width = cell->parameters.at(RTLIL::IdString("\\WIDTH")).as_int();
				int l1 = dump_sigspec(&cell->getPort(RTLIL::IdString("\\A")), output_width);
				int l2 = dump_sigspec(&cell->getPort(RTLIL::IdString("\\B")), output_width);
				int s = dump_sigspec(&cell->getPort(RTLIL::IdString("\\S")), 1);
				++line_num;
				str = stringf ("%d %s %d %d %d %d",
					line_num, cell_type_translation.at(cell->type.str()).c_str(), output_width, s, l2, l1);
				//if s is 0 then l1, if s is 1 then l2 //according to the implementation of mux cell
				f << stringf("%s\n", str.c_str());
				line_ref[cell->name]=line_num;
			}
			else if(cell->type == "$pmux")
                        {
                          log("writing pmux cell\n");
                          int output_width = cell->parameters.at(RTLIL::IdString("\\WIDTH")).as_int();
                          int select_width = cell->parameters.at(RTLIL::IdString("\\S_WIDTH")).as_int();
                          int default_case = dump_sigspec(&cell->getPort(RTLIL::IdString("\\A")), output_width);
                          int cases = dump_sigspec(&cell->getPort(RTLIL::IdString("\\B")), output_width*select_width);
                          int select = dump_sigspec(&cell->getPort(RTLIL::IdString("\\S")), select_width);
                          int *c = new int[select_width];

                          for (int i=0; i<select_width; ++i)
                          {
                            ++line_num;
                            str = stringf ("%d slice 1 %d %d %d", line_num, select, i, i);
                            f << stringf("%s\n", str.c_str());
                            c[i] = line_num;
                            ++line_num;
                            str = stringf ("%d slice %d %d %d %d", line_num, output_width, cases, i*output_width+output_width-1,
                                           i*output_width);
                            f << stringf("%s\n", str.c_str());
                          }

                          ++line_num;
                          str = stringf ("%d cond %d %d %d %d", line_num, output_width, c[select_width-1], c[select_width-1]+1, default_case);
                          f << stringf("%s\n", str.c_str());

                          for (int i=select_width-2; i>=0; --i)
                          {
                            ++line_num;
                            str = stringf ("%d cond %d %d %d %d", line_num, output_width, c[i], c[i]+1, line_num-1);
                            f << stringf("%s\n", str.c_str());
                          }

                          line_ref[cell->name]=line_num;
                        }
            //registers
			else if(cell->type == "$dff" || cell->type == "$adff" || cell->type == "$dffsr")
			{
				//TODO: remodelling of adff cells
				log("writing cell - %s\n", cstr(cell->type));
				int output_width = cell->parameters.at(RTLIL::IdString("\\WIDTH")).as_int();
				log(" - width is %d\n", output_width);
				int cond = dump_sigspec(&cell->getPort(RTLIL::IdString("\\CLK")), 1);
				bool polarity = cell->parameters.at(RTLIL::IdString("\\CLK_POLARITY")).as_bool();
				const RTLIL::SigSpec* cell_output = &cell->getPort(RTLIL::IdString("\\Q"));
				int value = dump_sigspec(&cell->getPort(RTLIL::IdString("\\D")), output_width);
				unsigned start_bit = 0;
				for(unsigned i=0; i<cell_output->chunks().size(); ++i)
				{
					output_width = cell_output->chunks().at(i).width;
					log_assert( output_width == cell_output->chunks().at(i).wire->width);//full reg is given the next value
					int reg = dump_wire(cell_output->chunks().at(i).wire);//register
					int slice = value;
					if(cell_output->chunks().size()>1)
					{
						start_bit+=output_width;
						slice = ++line_num;
						str = stringf ("%d slice %d %d %d %d;", line_num, output_width, value, start_bit-1,
							start_bit-output_width);
						f << stringf("%s\n", str.c_str());
					}
					if(cell->type == "$dffsr")
					{
						int sync_reset = dump_sigspec(&cell->getPort(RTLIL::IdString("\\CLR")), 1);
						bool sync_reset_pol = cell->parameters.at(RTLIL::IdString("\\CLR_POLARITY")).as_bool();
						int sync_reset_value = dump_sigspec(&cell->getPort(RTLIL::IdString("\\SET")),
							output_width);
						bool sync_reset_value_pol = cell->parameters.at(RTLIL::IdString("\\SET_POLARITY")).as_bool();
						++line_num;
						str = stringf ("%d %s %d %s%d %s%d %d", line_num, cell_type_translation.at("$mux").c_str(),
							output_width, sync_reset_pol ? "":"-", sync_reset, sync_reset_value_pol? "":"-",
							sync_reset_value, slice);
						f << stringf("%s\n", str.c_str());
						slice = line_num;
					}
					++line_num;
					str = stringf ("%d %s %d %s%d %d %d", line_num, cell_type_translation.at("$mux").c_str(),
						output_width, polarity?"":"-", cond, slice, reg);

					f << stringf("%s\n", str.c_str());
					int next = line_num;
					if(cell->type == "$adff")
					{
						int async_reset = dump_sigspec(&cell->getPort(RTLIL::IdString("\\ARST")), 1);
						bool async_reset_pol = cell->parameters.at(RTLIL::IdString("\\ARST_POLARITY")).as_bool();
						int async_reset_value = dump_const(&cell->parameters.at(RTLIL::IdString("\\ARST_VALUE")),
							output_width, 0);
						++line_num;
						str = stringf ("%d %s %d %s%d %d %d", line_num, cell_type_translation.at("$mux").c_str(),
							output_width, async_reset_pol ? "":"-", async_reset, async_reset_value, next);
						f << stringf("%s\n", str.c_str());
					}
					++line_num;
					str = stringf ("%d %s %d %d %d", line_num, cell_type_translation.at(cell->type.str()).c_str(),
						output_width, reg, next);
					f << stringf("%s\n", str.c_str());
				}
				line_ref[cell->name]=line_num;
			}
			//memories
			else if(cell->type == "$memrd")
			{
				log("writing memrd cell\n");
				if (cell->parameters.at("\\CLK_ENABLE").as_bool() == true)
					log_error("The btor backen does not support $memrd cells with built-in registers. Run memory_dff with -wr_only.\n");
				str = cell->parameters.at(RTLIL::IdString("\\MEMID")).decode_string();
				int mem = dump_memory(module->memories.at(RTLIL::IdString(str.c_str())));
				int address_width = cell->parameters.at(RTLIL::IdString("\\ABITS")).as_int();
				int address = dump_sigspec(&cell->getPort(RTLIL::IdString("\\ADDR")), address_width);
				int data_width = cell->parameters.at(RTLIL::IdString("\\WIDTH")).as_int();
				++line_num;
				str = stringf("%d read %d %d %d", line_num, data_width, mem, address);
				f << stringf("%s\n", str.c_str());
				line_ref[cell->name]=line_num;
			}
			else if(cell->type == "$memwr")
			{
				log("writing memwr cell\n");
				if (cell->parameters.at("\\CLK_ENABLE").as_bool() == false)
					log_error("The btor backen does not support $memwr cells without built-in registers. Run memory_dff (but with -wr_only).\n");
				int clk = dump_sigspec(&cell->getPort(RTLIL::IdString("\\CLK")), 1);
				bool polarity = cell->parameters.at(RTLIL::IdString("\\CLK_POLARITY")).as_bool();
				int enable = dump_sigspec(&cell->getPort(RTLIL::IdString("\\EN")), 1);
				int address_width = cell->parameters.at(RTLIL::IdString("\\ABITS")).as_int();
				int address = dump_sigspec(&cell->getPort(RTLIL::IdString("\\ADDR")), address_width);
				int data_width = cell->parameters.at(RTLIL::IdString("\\WIDTH")).as_int();
				int data = dump_sigspec(&cell->getPort(RTLIL::IdString("\\DATA")), data_width);
				str = cell->parameters.at(RTLIL::IdString("\\MEMID")).decode_string();
				int mem = dump_memory(module->memories.at(RTLIL::IdString(str.c_str())));
				//check if the memory has already next
                                /*
				auto it = mem_next.find(mem);
                                if(it != std::end(mem_next))
                                {
                                        ++line_num;
                                        str = cell->parameters.at(RTLIL::IdString("\\MEMID")).decode_string();
                                        RTLIL::Memory *memory = module->memories.at(RTLIL::IdString(str.c_str()));
                                        int address_bits = ceil_log2(memory->size);
                                        str = stringf("%d array %d %d", line_num, memory->width, address_bits);
                                        f << stringf("%s\n", str.c_str());
                                        ++line_num;
                                        str = stringf("%d eq 1 %d %d; mem invar", line_num, mem, line_num - 1);
                                        f << stringf("%s\n", str.c_str());
                                        mem = line_num - 1;
				}
				*/
				++line_num;
				if(polarity)
					str = stringf("%d one 1", line_num);
				else
					str = stringf("%d zero 1", line_num);
				f << stringf("%s\n", str.c_str());
				++line_num;
				str = stringf("%d eq 1 %d %d", line_num, clk, line_num-1);
				f << stringf("%s\n", str.c_str());
				++line_num;
				str = stringf("%d and 1 %d %d", line_num, line_num-1, enable);
				f << stringf("%s\n", str.c_str());
				++line_num;
				str = stringf("%d write %d %d %d %d %d", line_num, data_width, address_width, mem, address, data);
				f << stringf("%s\n", str.c_str());
				/*
				++line_num;
				str = stringf("%d acond %d %d %d %d %d", line_num, data_width, address_width, line_num-2, line_num-1, mem);
				f << stringf("%s\n", str.c_str());
				++line_num;
				str = stringf("%d anext %d %d %d %d", line_num, data_width, address_width, mem, line_num-1);
				f << stringf("%s\n", str.c_str());
				*/
				mem_next[mem].insert(std::make_pair(line_num-1, line_num));
			}
			else if(cell->type == "$slice")
			{
				log("writing slice cell\n");
				const RTLIL::SigSpec* input = &cell->getPort(RTLIL::IdString("\\A"));
				int input_width = cell->parameters.at(RTLIL::IdString("\\A_WIDTH")).as_int();
				log_assert(input->size() == input_width);
				int input_line = dump_sigspec(input, input_width);
				const RTLIL::SigSpec* output YS_ATTRIBUTE(unused) = &cell->getPort(RTLIL::IdString("\\Y"));
				int output_width = cell->parameters.at(RTLIL::IdString("\\Y_WIDTH")).as_int();
				log_assert(output->size() == output_width);
				int offset = cell->parameters.at(RTLIL::IdString("\\OFFSET")).as_int();
				++line_num;
				str = stringf("%d %s %d %d %d %d", line_num, cell_type_translation.at(cell->type.str()).c_str(), output_width, input_line, output_width+offset-1, offset);
				f << stringf("%s\n", str.c_str());
				line_ref[cell->name]=line_num;
			}
			else if(cell->type == "$concat")
			{
				log("writing concat cell\n");
				const RTLIL::SigSpec* input_a = &cell->getPort(RTLIL::IdString("\\A"));
				int input_a_width = cell->parameters.at(RTLIL::IdString("\\A_WIDTH")).as_int();
				log_assert(input_a->size() == input_a_width);
				int input_a_line = dump_sigspec(input_a, input_a_width);
				const RTLIL::SigSpec* input_b = &cell->getPort(RTLIL::IdString("\\B"));
				int input_b_width = cell->parameters.at(RTLIL::IdString("\\B_WIDTH")).as_int();
				log_assert(input_b->size() == input_b_width);
				int input_b_line = dump_sigspec(input_b, input_b_width);
				++line_num;
				str = stringf("%d %s %d %d %d", line_num, cell_type_translation.at(cell->type.str()).c_str(), input_a_width+input_b_width,
					input_a_line, input_b_line);
				f << stringf("%s\n", str.c_str());
				line_ref[cell->name]=line_num;
			}
			curr_cell.clear();
			return line_num;
		}
		else
		{
			return it->second;
		}
	}

	const RTLIL::SigSpec* get_cell_output(RTLIL::Cell* cell)
	{
		const RTLIL::SigSpec *output_sig = nullptr;
		if (cell->type == "$memrd")
		{
			output_sig = &cell->getPort(RTLIL::IdString("\\DATA"));
		}
		else if(cell->type == "$memwr" || cell->type == "$assert")
		{
			//no output
		}
		else if(cell->type == "$dff" || cell->type == "$adff" || cell->type == "$dffsr")
		{
			output_sig = &cell->getPort(RTLIL::IdString("\\Q"));
		}
		else
		{
			output_sig = &cell->getPort(RTLIL::IdString("\\Y"));
		}
		return output_sig;
	}

	void dump_property(RTLIL::Wire *wire)
	{
		int l = dump_wire(wire);
		++line_num;
		str = stringf("%d root 1 %d", line_num, l);
		f << stringf("%s\n", str.c_str());
	}

	void dump()
	{
		f << stringf(";module %s\n", cstr(module->name));

		log("creating intermediate wires map\n");
		//creating map of intermediate wires as output of some cell
		for (auto it = module->cells_.begin(); it != module->cells_.end(); ++it)
		{
			RTLIL::Cell *cell = it->second;
			const RTLIL::SigSpec* output_sig = get_cell_output(cell);
			if(output_sig==nullptr)
				continue;
			RTLIL::SigSpec s = sigmap(*output_sig);
			output_sig = &s;
			log(" - %s\n", cstr(it->second->type));
			if (cell->type == "$memrd")
			{
				for(unsigned i=0; i<output_sig->chunks().size(); ++i)
				{
					RTLIL::Wire *w = output_sig->chunks().at(i).wire;
					RTLIL::IdString wire_id = w->name;
					inter_wire_map[wire_id].insert(WireInfo(cell->name,&output_sig->chunks().at(i)));
				}
			}
			else if(cell->type == "$memwr")
			{
				continue;//nothing to do
			}
			else if(cell->type == "$dff" || cell->type == "$adff" || cell->type == "$dffsr")
			{
				RTLIL::IdString wire_id = output_sig->chunks().front().wire->name;
				for(unsigned i=0; i<output_sig->chunks().size(); ++i)
				{
					RTLIL::Wire *w = output_sig->chunks().at(i).wire;
					RTLIL::IdString wire_id = w->name;
					inter_wire_map[wire_id].insert(WireInfo(cell->name,&output_sig->chunks().at(i)));
					basic_wires[wire_id] = true;
				}
			}
			else
			{
				for(unsigned i=0; i<output_sig->chunks().size(); ++i)
				{
					RTLIL::Wire *w = output_sig->chunks().at(i).wire;
					RTLIL::IdString wire_id = w->name;
					inter_wire_map[wire_id].insert(WireInfo(cell->name,&output_sig->chunks().at(i)));
				}
			}
		}

		log("writing input\n");
		std::map<int, RTLIL::Wire*> inputs, outputs;
		std::vector<RTLIL::Wire*> safety;

		for (auto &wire_it : module->wires_) {
			RTLIL::Wire *wire = wire_it.second;
			if (wire->port_input)
				inputs[wire->port_id] = wire;
			if (wire->port_output) {
				outputs[wire->port_id] = wire;
				if (wire->name.str().find("safety") != std::string::npos )
					safety.push_back(wire);
			}
		}

		f << stringf(";inputs\n");
		for (auto &it : inputs) {
			RTLIL::Wire *wire = it.second;
			dump_wire(wire);
		}
		f << stringf("\n");

		log("writing memories\n");
		for(auto mem_it = module->memories.begin(); mem_it != module->memories.end(); ++mem_it)
		{
			dump_memory(mem_it->second);
		}

		log("writing output wires\n");
		for (auto &it : outputs) {
			RTLIL::Wire *wire = it.second;
			dump_wire(wire);
		}

		log("writing cells\n");
		for(auto cell_it = module->cells_.begin(); cell_it != module->cells_.end(); ++cell_it)
		{
			dump_cell(cell_it->second);
		}

		log("writing memory next");
		for(auto mem_it = module->memories.begin(); mem_it != module->memories.end(); ++mem_it)
		  {
		    dump_memory_next(mem_it->second);
		  }

		for(auto it: safety)
			dump_property(it);

		f << stringf("\n");

		log("writing outputs info\n");
		f << stringf(";outputs\n");
		for (auto &it : outputs) {
			RTLIL::Wire *wire = it.second;
			int l = dump_wire(wire);
			f << stringf(";%d %s", l, cstr(wire->name));
		}
		f << stringf("\n");
	}

	static void dump(std::ostream &f, RTLIL::Module *module, RTLIL::Design *design, BtorDumperConfig &config)
	{
		BtorDumper dumper(f, module, design, &config);
		dumper.dump();
	}
};

struct BtorBackend : public Backend {
	BtorBackend() : Backend("btor", "write design to BTOR file") { }

	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    write_btor [filename]\n");
		log("\n");
		log("Write the current design to an BTOR file.\n");
	}

	virtual void execute(std::ostream *&f, std::string filename, std::vector<std::string> args, RTLIL::Design *design)
	{
		std::string top_module_name;
		std::string buf_type, buf_in, buf_out;
		std::string true_type, true_out;
		std::string false_type, false_out;
		BtorDumperConfig config;

		log_header(design, "Executing BTOR backend.\n");

		size_t argidx=1;
		extra_args(f, filename, args, argidx);

		if (top_module_name.empty())
			for (auto & mod_it:design->modules_)
				if (mod_it.second->get_bool_attribute("\\top"))
					top_module_name = mod_it.first.str();

		*f << stringf("; Generated by %s\n", yosys_version_str);
		*f << stringf(";  %s developed and maintained by Clifford Wolf <clifford@clifford.at>\n", yosys_version_str);
		*f << stringf("; BTOR Backend developed by Ahmed Irfan <irfan@fbk.eu> - Fondazione Bruno Kessler, Trento, Italy\n");
		*f << stringf(";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n");

		std::vector<RTLIL::Module*> mod_list;

		for (auto module_it : design->modules_)
		{
			RTLIL::Module *module = module_it.second;
			if (module->get_bool_attribute("\\blackbox"))
				continue;

			if (module->processes.size() != 0)
				log_error("Found unmapped processes in module %s: unmapped processes are not supported in BTOR backend!\n", RTLIL::id2cstr(module->name));

			if (module->name == RTLIL::escape_id(top_module_name)) {
				BtorDumper::dump(*f, module, design, config);
				top_module_name.clear();
				continue;
			}

			mod_list.push_back(module);
		}

		if (!top_module_name.empty())
			log_error("Can't find top module `%s'!\n", top_module_name.c_str());

		for (auto module : mod_list)
			BtorDumper::dump(*f, module, design, config);
	}
} BtorBackend;

PRIVATE_NAMESPACE_END
