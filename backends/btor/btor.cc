/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Clifford Wolf <clifford@clifford.at>
 *  Copyright (C) 2013  Ahmed Irfan <ahmedirfan1983@gmail.com>
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
#include <queue>
#include <assert.h>
#include <math.h>

struct BtorDumperConfig
{
	bool subckt_mode;
	bool conn_mode;
	bool impltf_mode;

	std::string buf_type, buf_in, buf_out;
	std::string true_type, true_out, false_type, false_out;

	BtorDumperConfig() : subckt_mode(false), conn_mode(false), impltf_mode(false) { }
};

struct BtorDumper
{
	FILE *f;
	RTLIL::Module *module;
	RTLIL::Design *design;
	BtorDumperConfig *config;
	CellTypes ct;

	std::map<RTLIL::IdString, std::vector<RTLIL::IdString>> inter_wire_map;//<wire, dependency list> for maping the intermediate wires that are output of some cell  
	std::map<RTLIL::IdString, int> line_ref;//mapping of ids to line_num of the btor file
	int line_num;//last line number of btor file
	std::string str;//temp string
	std::queue<RTLIL::SigSig> conn_list;
	std::map<RTLIL::IdString, bool> basic_wires;//input wires and wires with dff	
	RTLIL::IdString curr_cell;
	std::map<std::string, std::string> cell_type_translation;	
	BtorDumper(FILE *f, RTLIL::Module *module, RTLIL::Design *design, BtorDumperConfig *config) :
			f(f), module(module), design(design), config(config), ct(design)
	{
		line_num=0;
		str.clear();
		for(auto it=module->connections.begin(); it !=module->connections.end(); it++)
		{
			conn_list.push(*it);
		}
		for(auto it=module->wires.begin(); it!=module->wires.end(); it++)
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
		cell_type_translation = { 
					//unary
					{"$not","not"},{"$neg","neg"},{"$reduce_and","redand"},
					{"$reduce_or","redor"},{"$reduce_xor","redxor"},{"$reduce_bool","redor"},
					//binary
					{"$and","and"},{"$or","or"},{"$xor","xor"},{"$xnor","xnor"},
					{"$shr","srl"},{"$shl","sll"},{"$sshr","sra"},{"$sshl","sll"},
					{"$lt","ult"},{"$le","ulte"},{"$eq","eq"},{"$ne","ne"},{"$gt","ugt"},{"$ge","ugte"},
					{"$add","add"},{"$sub","sub"},{"$mul","mul"},{"$mod","urem"},{"$div","udiv"},
					//mux
					{"$mux","cond"},
					//reg
					{"$dff","next"},{"$adff","next"},{"$dffsr","next"}
					//memories
					};
	}
	
	std::vector<std::string> cstr_buf;

	const char *cstr(const RTLIL::IdString id)
	{
		str = RTLIL::unescape_id(id);
		for (size_t i = 0; i < str.size(); i++)
			if (str[i] == '#' || str[i] == '=')
				str[i] = '?';
		cstr_buf.push_back(str);
		return cstr_buf.back().c_str();
	}
	
	int dump_wire(const RTLIL::Wire* wire)
	{
		log("writing wire %s\n", cstr(wire->name));
		if(basic_wires[wire->name])
		{	
			auto it = line_ref.find(wire->name);
			if(it==std::end(line_ref))
			{
				line_num++;
				line_ref[wire->name]=line_num;			
				str = stringf("%d var %d %s", line_num, wire->width, cstr(wire->name));
				fprintf(f, "%s\n", str.c_str());
				return line_num;
			}
			else return it->second;
		}
		else // case when the wire is intermediate wire (auto generated)
		{
			log(" - case of intermediate wire - %s\n", cstr(wire->name));
			auto it = line_ref.find(wire->name);
			if(it==std::end(line_ref))
			{
				auto cell_it = inter_wire_map.find(wire->name);
				if(cell_it !=std::end(inter_wire_map) && cell_it->second != curr_cell)
				{
					log(" -- found cell %s\n", cstr(cell_it->second));
					RTLIL::Cell *cell = module->cells.at(cell_it->second);
					int l = dump_cell(cell);
					line_ref[wire->name] = l;
					return l; 
				}
				else
				{
					log(" -- checking connections\n");
					for(unsigned i=0; i<conn_list.size(); i++)
					{
						log(" --- checking %d\n", i);
						RTLIL::SigSig ss = conn_list.front();
						conn_list.pop();
						RTLIL::SigSpec *sig1 = &ss.first;
						RTLIL::SigSpec *sig2 = &ss.second;
						unsigned sig1_wires_count = sig1->chunks.size();
						unsigned sig2_wires_count = sig2->chunks.size();
						int start_bit=sig1->width-1;
						for(unsigned j=0; j<sig1_wires_count; j++)
						{
							if(sig1->chunks[j].wire!=NULL && sig1->chunks[j].wire->name == wire->name && sig1->chunks[j].offset == 0)
							{
								log(" ---- found match sig1\n");
								conn_list.push(ss);
								if(sig1_wires_count == 1)
								{
									int l = dump_sigspec(sig2, sig2->width);
									line_ref[wire->name] = l;
									return l;
								}
								else
								{
									int l = dump_sigspec(sig2, sig2->width);
									line_num++;
									str = stringf("%d slice %d %d %d %d", line_num, wire->width, l, start_bit, start_bit-wire->width+1);
									fprintf(f, "%s\n", str.c_str());
									line_ref[wire->name]=line_num;
									return line_num;
								}							
							}
							start_bit-=sig1->chunks[j].width;	
						}						
						start_bit=sig2->width-1;
						for(unsigned j=0; j<sig2_wires_count; j++)
						{
							if(sig2->chunks[j].wire!=NULL && sig2->chunks[j].wire->name == wire->name && sig2->chunks[j].offset == 0)
							{
								log(" ---- found match sig2\n");
								conn_list.push(ss);
								if(sig2_wires_count == 1)
								{
									int l = dump_sigspec(sig1, sig1->width);
									line_ref[wire->name] = l;
									return l;
								}
								else
								{
									int l = dump_sigspec(sig1, sig1->width);
									line_num++;
									str = stringf("%d slice %d %d %d %d", line_num, wire->width, l, start_bit, start_bit-wire->width+1);
									fprintf(f, "%s\n", str.c_str());
									line_ref[wire->name]=line_num;
									return line_num;
								}							
							}
							start_bit-=sig2->chunks[j].width;	
						}
						conn_list.push(ss);
					}
					log(" --- nothing found\n");
					return -1;
				}
			}
			else 
			{
				log(" -- already processed wire\n");			
				return it->second;
			}
		}
	}
	
	int dump_memory(const RTLIL::Memory* memory)
	{
		log("writing memory %s\n", cstr(memory->name));
		auto it = line_ref.find(memory->name);
		if(it==std::end(line_ref))
		{
			line_num++;
			int address_bits = ceil(log(memory->size)/log(2));
			str = stringf("%d array %d %d", line_num, memory->width, address_bits);
			line_ref[memory->name]=line_num;			
			fprintf(f, "%s\n", str.c_str());
			return line_num;
		}
		else return it->second;
	}

	int dump_const(const RTLIL::Const* data, int width, int offset)
	{
		log("writing const \n");
		if((data->flags & RTLIL::CONST_FLAG_STRING) == 0)
		{
			if(width<0)
				width = data->bits.size() - offset;

			std::string data_str = data->as_string();
			if(offset > 0)
				data_str = data_str.substr(offset, width);

			line_num++;
			str = stringf("%d const %d %s", line_num, width, data_str.c_str());
			fprintf(f, "%s\n", str.c_str());
			return line_num;
		}
		else
			log("writing const error\n");		
		return -1;
	}
	
	int dump_sigchunk(const RTLIL::SigChunk* chunk)
	{
		log("writing sigchunk\n");
		int l=-1;
		if(chunk->wire == NULL)
		{
			l=dump_const(&chunk->data, chunk->width, chunk->offset);			
		}
		else
		{
			if (chunk->width == chunk->wire->width && chunk->offset == 0)
				l = dump_wire(chunk->wire);
			else 
			{
				str = stringf("%s[%d:%d]", chunk->wire->name.c_str(), 
					chunk->offset + chunk->width - 1, chunk->offset);
				auto it = line_ref.find(RTLIL::IdString(str));
				if(it==std::end(line_ref))
				{
					int wire_line_num = dump_wire(chunk->wire);
					if(wire_line_num<=0)
						return -1;
					line_num++;
					line_ref[RTLIL::IdString(str)] = line_num;
					str = stringf("%d slice %d %d %d %d", line_num, chunk->width, 
						wire_line_num, chunk->offset + chunk->width - 1, chunk->offset);
					fprintf(f, "%s\n", str.c_str());
					l = line_num;				 
				}
				else
					l=it->second;
			}
		}
		return l;
	}

	int dump_sigspec(const RTLIL::SigSpec* sig, int expected_width)
	{
		log("writing sigspec\n");
		assert(sig->width<=expected_width);
		int l = -1;
		if (sig->chunks.size() == 1) 
		{
			l = dump_sigchunk(&sig->chunks[0]);
		} 
		else 
		{
			int l1, l2, w1, w2;
			l1 = dump_sigchunk(&sig->chunks[0]);
			if(l1<=0)
				return -1;
			w1 = sig->chunks[0].width;
			for (unsigned i=1; i < sig->chunks.size(); i++)
			{
				l2 = dump_sigchunk(&sig->chunks[i]);
				if(l2<=0)
					return -1;
				w2 = sig->chunks[i].width;
				line_num++;
				str = stringf("%d concat %d %d %d", line_num, w1+w2, l2, l1);
				fprintf(f, "%s\n", str.c_str());
				l1=line_num;
				w1+=w2;
			}
			l = line_num;
		}
		if(expected_width > sig->width)
		{
			line_num++;
			str = stringf ("%d zero %d", line_num, expected_width - sig->width);
			fprintf(f, "%s\n", str.c_str());
			line_num++;
			str = stringf ("%d concat %d %d %d", line_num, expected_width, line_num-1, l);
			fprintf(f, "%s\n", str.c_str());
			l = line_num;
		}
		return l;
	}
	
	int dump_cell(const RTLIL::Cell* cell)
	{
		auto it = line_ref.find(cell->name);
		if(it==std::end(line_ref))
		{
			curr_cell = cell->name;
			//unary cells
			if(cell->type == "$not" || cell->type == "$neg" || cell->type == "$pos" || cell->type == "$reduce_and" ||
				cell->type == "$reduce_or" || cell->type == "$reduce_xor" || cell->type == "$reduce_bool")
			{
				log("writing unary cell - %s\n", cstr(cell->type));
				RTLIL::IdString output_id = cell->connections.at(RTLIL::IdString("\\Y")).chunks[0].wire->name;//output wire name
				int w = cell->parameters.at(RTLIL::IdString("\\A_WIDTH")).as_int();
				int output_width = cell->parameters.at(RTLIL::IdString("\\Y_WIDTH")).as_int();
				assert((cell->type == "$not" || cell->type == "$neg") && w==output_width);
				int l = dump_sigspec(&cell->connections.at(RTLIL::IdString("\\A")), w);				
				if(cell->type == "$pos")
					return l;				
				line_num++;
				line_ref[output_id]=line_num;
				line_ref[cell->name]=line_num;
				str = stringf ("%d %s %d %d", line_num, cell_type_translation.at(cell->type).c_str(), output_width, l);
				fprintf(f, "%s\n", str.c_str());
			}
			else if(cell->type == "$reduce_xnor" || cell->type == "$logic_not")//no direct translation in btor
			{
				log("writing unary cell - %s\n", cstr(cell->type));
				RTLIL::IdString output_id = cell->connections.at(RTLIL::IdString("\\Y")).chunks[0].wire->name;//output wire name
				int w = cell->parameters.at(RTLIL::IdString("\\A_WIDTH")).as_int();
				int output_width = cell->parameters.at(RTLIL::IdString("\\Y_WIDTH")).as_int();
				int l = dump_sigspec(&cell->connections.at(RTLIL::IdString("\\A")), w);
				if(cell->type == "$logic_not")
				{
					line_num++;
					str = stringf ("%d %s %d %d", line_num, cell_type_translation.at("$reduce_or").c_str(), output_width, l);
					fprintf(f, "%s\n", str.c_str());
				}
				else if(cell->type == "$reduce_xnor")
				{
					line_num++;
					str = stringf ("%d %s %d %d", line_num, cell_type_translation.at("$reduce_xor").c_str(), output_width, l);
					fprintf(f, "%s\n", str.c_str());
				}		
				line_ref[output_id]=line_num;
				line_ref[cell->name]=line_num;
				line_num++;
				str = stringf ("%d %s %d %d", line_num, cell_type_translation.at("$not").c_str(), output_width, line_num-1);
				fprintf(f, "%s\n", str.c_str());
			}
			//binary cells
			else if(cell->type == "$and" || cell->type == "$or" || cell->type == "$xor" || cell->type == "$xnor" ||
				 cell->type == "$add" || cell->type == "$sub" || cell->type == "$mul" || cell->type == "$div" || 
				 cell->type == "$mod" || cell->type == "$lt" || cell->type == "$le" || cell->type == "$eq" || 
				 cell->type == "$ne" || cell->type == "$ge" || cell->type == "$gt" || 
				 cell->type == "$shr" || cell->type == "$shl" || cell->type == "$sshr" || cell->type == "$sshl")
			{
				log("writing binary cell - %s\n", cstr(cell->type));
				RTLIL::IdString output_id = cell->connections.at(RTLIL::IdString("\\Y")).chunks[0].wire->name;//output wire name
				int output_width = cell->parameters.at(RTLIL::IdString("\\Y_WIDTH")).as_int();
				int l1 = dump_sigspec(&cell->connections.at(RTLIL::IdString("\\A")), output_width);
				int l2 = dump_sigspec(&cell->connections.at(RTLIL::IdString("\\B")), output_width);
				line_num++;
				line_ref[output_id]=line_num;
				line_ref[cell->name]=line_num;
				str = stringf ("%d %s %d %d %d", 
					line_num, cell_type_translation.at(cell->type).c_str(), output_width, l1, l2);
				fprintf(f, "%s\n", str.c_str());
			}
			else if(cell->type == "$logic_and" || cell->type == "$logic_or")//no direct translation in btor
			{
				log("writing binary cell - %s\n", cstr(cell->type));
				RTLIL::IdString output_id = cell->connections.at(RTLIL::IdString("\\Y")).chunks[0].wire->name;//output wire name
				int output_width = cell->parameters.at(RTLIL::IdString("\\Y_WIDTH")).as_int();
				int l1 = dump_sigspec(&cell->connections.at(RTLIL::IdString("\\A")), output_width);
				int l2 = dump_sigspec(&cell->connections.at(RTLIL::IdString("\\B")), output_width);
				line_num++;
				str = stringf ("%d %s %d %d", line_num, cell_type_translation.at("$reduce_or").c_str(), output_width, l1);
				fprintf(f, "%s\n", str.c_str());
				line_num++;
				str = stringf ("%d %s %d %d", line_num, cell_type_translation.at("$reduce_or").c_str(), output_width, l2);
				fprintf(f, "%s\n", str.c_str());
				if(cell->type == "$logic_and")
				{
					line_num++;
					str = stringf ("%d %s %d %d %d", line_num, cell_type_translation.at("$and").c_str(), output_width, line_num-2, line_num-1);
				}
				else if(cell->type == "$logic_or")
				{
					line_num++;
					str = stringf ("%d %s %d %d %d", line_num, cell_type_translation.at("$or").c_str(), output_width, line_num-2, line_num-1);
				}
				line_ref[output_id]=line_num;
				line_ref[cell->name]=line_num;
				fprintf(f, "%s\n", str.c_str());
			}
			//multiplexers
			else if(cell->type == "$mux")
			{
				log("writing mux cell\n");
				RTLIL::IdString output_id = cell->connections.at(RTLIL::IdString("\\Y")).chunks[0].wire->name;//output wire name
				int output_width = cell->parameters.at(RTLIL::IdString("\\WIDTH")).as_int();
				int l1 = dump_sigspec(&cell->connections.at(RTLIL::IdString("\\A")), output_width);
				int l2 = dump_sigspec(&cell->connections.at(RTLIL::IdString("\\B")), output_width);
				int s = dump_sigspec(&cell->connections.at(RTLIL::IdString("\\S")), 1);
				line_num++;
				line_ref[output_id]=line_num;
				line_ref[cell->name]=line_num;
				str = stringf ("%d %s %d %d %d %d", 
					line_num, cell_type_translation.at(cell->type).c_str(), output_width, s, l2, l1);//if s is 0 then l1, if s is 1 then l2 //according to the implementation of mux cell
				fprintf(f, "%s\n", str.c_str());
			}
			//registers
			else if(cell->type == "$dff" || cell->type == "$adff" || cell->type == "$dffsr")
			{
				log("writing cell - %s\n", cstr(cell->type));
				int output_width = cell->parameters.at(RTLIL::IdString("\\WIDTH")).as_int();
				int reg = dump_sigspec(&cell->connections.at(RTLIL::IdString("\\Q")), output_width);//register
				int cond = dump_sigspec(&cell->connections.at(RTLIL::IdString("\\CLK")), 1);
				bool polarity = cell->parameters.at(RTLIL::IdString("\\CLK_POLARITY")).as_bool();
				int value = dump_sigspec(&cell->connections.at(RTLIL::IdString("\\D")), output_width);
				if(cell->type == "$dffsr")
				{
					int sync_reset = dump_sigspec(&cell->connections.at(RTLIL::IdString("\\CLR")), 1);
					bool sync_reset_pol = cell->parameters.at(RTLIL::IdString("\\CLR_POLARITY")).as_bool();
					int sync_reset_value = dump_sigspec(&cell->connections.at(RTLIL::IdString("\\SET")), output_width);
					bool sync_reset_value_pol = cell->parameters.at(RTLIL::IdString("\\SET_POLARITY")).as_bool();
					line_num++;
					str = stringf ("%d %s %d %s%d %s%d %d", line_num, cell_type_translation.at("$mux").c_str(), 
						output_width, sync_reset_pol ? "":"-", sync_reset, sync_reset_value_pol? "":"-", 
						sync_reset_value, value);
					fprintf(f, "%s\n", str.c_str());
					value = line_num;
				}
				line_num++;
				str = stringf ("%d %s %d %s%d %d %d", line_num, cell_type_translation.at("$mux").c_str(), 
					output_width, polarity?"":"-", cond, value, reg);
				
				fprintf(f, "%s\n", str.c_str());
				int next = line_num;
				if(cell->type == "$adff")
				{
					int async_reset = dump_sigspec(&cell->connections.at(RTLIL::IdString("\\ARST")), 1);
					bool async_reset_pol = cell->parameters.at(RTLIL::IdString("\\ARST_POLARITY")).as_bool();
					int async_reset_value = dump_const(&cell->parameters.at(RTLIL::IdString("\\ARST_VALUE")),
						output_width, 0);
					line_num++;
					str = stringf ("%d %s %d %s%d %d %d", line_num, cell_type_translation.at("$mux").c_str(), 
						output_width, async_reset_pol ? "":"-", async_reset, async_reset_value, next);
					fprintf(f, "%s\n", str.c_str());
				}
				line_num++;
				line_ref[cell->name]=line_num;
				str = stringf ("%d %s %d %d %d", 
					line_num, cell_type_translation.at(cell->type).c_str(), output_width, reg, next);
				fprintf(f, "%s\n", str.c_str());
			}
			//memories
			else if(cell->type == "$memrd")
			{
				log("writing memrd cell\n");
				RTLIL::IdString output_id = cell->connections.at(RTLIL::IdString("\\DATA")).chunks[0].wire->name;//output wire
				str = cell->parameters.at(RTLIL::IdString("\\MEMID")).decode_string();
				int mem = dump_memory(module->memories.at(RTLIL::IdString(str.c_str())));
				int address_width = cell->parameters.at(RTLIL::IdString("\\ABITS")).as_int();
				int address = dump_sigspec(&cell->connections.at(RTLIL::IdString("\\ADDR")), address_width);
				int data_width = cell->parameters.at(RTLIL::IdString("\\WIDTH")).as_int();
				line_num++;
				str = stringf("%d read %d %d %d", line_num, data_width, mem, address);	
				fprintf(f, "%s\n", str.c_str());
				line_ref[output_id]=line_num;
				line_ref[cell->name]=line_num;
			}
			else if(cell->type == "$memwr")
			{
				log("writing memwr cell\n");
				int clk = dump_sigspec(&cell->connections.at(RTLIL::IdString("\\CLK")), 1);
				bool polarity = cell->parameters.at(RTLIL::IdString("\\CLK_POLARITY")).as_bool();
				int enable = dump_sigspec(&cell->connections.at(RTLIL::IdString("\\EN")), 1);
				int address_width = cell->parameters.at(RTLIL::IdString("\\ABITS")).as_int();
				int address = dump_sigspec(&cell->connections.at(RTLIL::IdString("\\ADDR")), address_width);
				int data_width = cell->parameters.at(RTLIL::IdString("\\WIDTH")).as_int();
				int data = dump_sigspec(&cell->connections.at(RTLIL::IdString("\\DATA")), data_width);
				str = cell->parameters.at(RTLIL::IdString("\\MEMID")).decode_string();
				int mem = dump_memory(module->memories.at(RTLIL::IdString(str.c_str())));
				line_num++;
				if(polarity)
					str = stringf("%d one 1", line_num);
				else
					str = stringf("%d zero 1", line_num);
				fprintf(f, "%s\n", str.c_str());
				line_num++;
				str = stringf("%d eq 1 %d %d", line_num, clk, line_num-1);	
				fprintf(f, "%s\n", str.c_str());
				line_num++;
				str = stringf("%d and 1 %d %d", line_num, line_num-1, enable);	
				fprintf(f, "%s\n", str.c_str());
				line_num++;
				str = stringf("%d write %d %d %d %d %d", line_num, data_width, address_width, mem, address, data);	
				fprintf(f, "%s\n", str.c_str());
				line_num++;
				str = stringf("%d acond %d %d %d %d %d", line_num, data_width, address_width, line_num-2/*enable*/, line_num-1, mem);	
				fprintf(f, "%s\n", str.c_str());				
				line_num++;
				str = stringf("%d anext %d %d %d %d", line_num, data_width, address_width, mem, line_num-1);	
				fprintf(f, "%s\n", str.c_str());				
				line_ref[cell->name]=line_num;
			}
			return line_num;
		}
		else
		{
			return it->second;
		}
	}
	
	void dump()
	{
		fprintf(f, ";module %s\n", cstr(module->name));
		
		log("creating intermediate wires map\n");
		//creating map of intermediate wires as output of some cell
		for (auto it = module->cells.begin(); it != module->cells.end(); it++)
		{
			RTLIL::Cell *cell = it->second;
			log(" - %s\n", cstr(it->second->type));
			if (cell->type == "$memrd")
			{
				RTLIL::SigSpec *ss = &cell->connections.at(RTLIL::IdString("\\DATA"));
				for(int i=0; i<ss->chunks.size(); i++)
				{
					RTLIL::Wire *w = ss->chunks[i].wire;
					RTLIL::IdString wire_id = w->name;
					inter_wire_map[wire_id].push_back(cell->name);
				}
			}
			else if(it->second->type == "$memwr")
			{
				/*RTLIL::IdString wire_id = it->second->connections.at(RTLIL::IdString("\\MEMID")).chunks[0].wire->name;
				if(inter_wire_map.find(wire_id)==std::end(inter_wire_map))
					inter_wire_map[wire_id] = it->second->name;*/
			}
			else if(cell->type == "$dff" || cell->type == "$adff" || cell->type == "$dffsr")
			{
				RTLIL::IdString wire_id = cell->connections.at(RTLIL::IdString("\\Q")).chunks[0].wire->name;
				if(inter_wire_map.find(wire_id)==std::end(inter_wire_map))
				{
					inter_wire_map[wire_id] = it->second->name;
					basic_wires[wire_id] = true;
				}
			}
			else 
			{
				RTLIL::SigSpec *ss = &cell->connections.at(RTLIL::IdString("\\Y"));
				for(int i=0; i<ss->chunks.size(); i++)
				{
					RTLIL::Wire *w = ss->chunks[i].wire;
					RTLIL::IdString wire_id = w->name;
					inter_wire_map[wire_id].push_back(cell->name);
				}
			}
		}
		
		//removing duplicates
		for(auto it = inter_wire_map.begin(); it != inter_wire_map.end(); it++)
		{
			it->sort();
			unique(it->begin(), it->end());
		}

		log("writing input\n");
		std::map<int, RTLIL::Wire*> inputs;

		for (auto &wire_it : module->wires) {
			RTLIL::Wire *wire = wire_it.second;
			if (wire->port_input)
				inputs[wire->port_id] = wire;
		}

		fprintf(f, ";inputs\n");
		for (auto &it : inputs) {
			RTLIL::Wire *wire = it.second;
			for (int i = 0; i < wire->width; i++)
				dump_wire(wire);
		}
		fprintf(f, "\n");

		/*log("writing cells\n");
		fprintf(f, ";cells\n");
		for (auto it = module->cells.begin(); it != module->cells.end(); it++)
		{
			dump_cell(it->second);
		}

		log("writing connections\n");
		fprintf(f, ";output connections\n");
		for (auto it = module->connections.begin(); it != module->connections.end(); it++)
		{
			RTLIL::SigSpec *sig1 = &it->first;
			RTLIL::SigSpec *sig2 = &it->second;
			unsigned sig1_wires_count = sig1->chunks.size();
			unsigned sig2_wires_count = sig2->chunks.size();
			int start_bit=sig1->width-1;
			for(unsigned j=0; j<sig1_wires_count; j++)
			{
				if(sig1->chunks[j].wire!=NULL && sig1->chunks[j].wire->port_output)
				{
					if(sig1_wires_count == 1)
					{
						int next = dump_sigspec(sig2, sig2->width);
						int reg = dump_sigchunk(&sig1->chunks[j]);
						if(reg!=next)
						{
							line_num++;
							str = stringf("%d %s %d %d %d", line_num, cell_type_translation.at("$dff").c_str(),
								 sig1->chunks[j].width, reg, next);
							fprintf(f, "%s\n", str.c_str());
						}
					}
					else
					{
						int l = dump_sigspec(sig2, sig2->width);
						int reg = dump_sigchunk(&sig1->chunks[j]);
						line_num++;
						str = stringf("%d slice %d %d %d %d", line_num, sig1->chunks[j].width, l, start_bit, 
							start_bit-sig1->chunks[j].width+1);
						fprintf(f, "%s\n", str.c_str());
						line_num++;
						str = stringf("%d %s %d %d %d", line_num, cell_type_translation.at("$dff").c_str(),
							 sig1->chunks[j].width, reg, line_num-1);
						fprintf(f, "%s\n", str.c_str());
					}							
				}
				start_bit-=sig1->chunks[j].width;	
			}						
			start_bit=sig2->width-1;
			for(unsigned j=0; j<sig2_wires_count; j++)
			{
				if(sig2->chunks[j].wire!=NULL && sig2->chunks[j].wire->port_output)
				{
					if(sig2_wires_count == 1)
					{
						int next = dump_sigspec(sig1, sig1->width);
						int reg = dump_sigchunk(&sig2->chunks[j]);
						if(reg!=next)
						{
							line_num++;
							str = stringf("%d %s %d %d %d", line_num, cell_type_translation.at("$dff").c_str(),
								 sig2->chunks[j].width, reg, next);
							fprintf(f, "%s\n", str.c_str());
						}
					}
					else
					{
						int l = dump_sigspec(sig1, sig1->width);
						int reg = dump_sigchunk(&sig2->chunks[j]);
						line_num++;
						str = stringf("%d slice %d %d %d %d", line_num, sig2->chunks[j].width, l, start_bit, 
							start_bit-sig2->chunks[j].width+1);
						fprintf(f, "%s\n", str.c_str());
						line_num++;
						str = stringf("%d %s %d %d %d", line_num, cell_type_translation.at("$dff").c_str(),
							 sig2->chunks[j].width, reg, line_num-1);
						fprintf(f, "%s\n", str.c_str());
					}							
				}
				start_bit-=sig2->chunks[j].width;	
			}
		}*/
	}

	static void dump(FILE *f, RTLIL::Module *module, RTLIL::Design *design, BtorDumperConfig &config)
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

	virtual void execute(FILE *&f, std::string filename, std::vector<std::string> args, RTLIL::Design *design)
	{
		std::string top_module_name;
		std::string buf_type, buf_in, buf_out;
		std::string true_type, true_out;
		std::string false_type, false_out;
		BtorDumperConfig config;

		log_header("Executing BTOR backend.\n");

		size_t argidx=1;
		extra_args(f, filename, args, argidx);
		
		if (top_module_name.empty())
			for (auto & mod_it:design->modules)
				if (mod_it.second->get_bool_attribute("\\top"))
					top_module_name = mod_it.first;

		fprintf(f, "; Generated by %s\n", yosys_version_str);

		std::vector<RTLIL::Module*> mod_list;

		for (auto module_it : design->modules)
		{
			RTLIL::Module *module = module_it.second;
			if (module->get_bool_attribute("\\blackbox"))
				continue;

			if (module->name == RTLIL::escape_id(top_module_name)) {
				BtorDumper::dump(f, module, design, config);
				top_module_name.clear();
				continue;
			}

			mod_list.push_back(module);
		}

		if (!top_module_name.empty())
			log_error("Can't find top module `%s'!\n", top_module_name.c_str());

		for (auto module : mod_list)
			BtorDumper::dump(f, module, design, config);
	}
} BtorBackend;

