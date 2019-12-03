/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Clifford Wolf <clifford@clifford.at>
 *  Copyright (C) 2018  Serge Bazanski <q3k@symbioticeda.com>
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

#include <google/protobuf/text_format.h>

#include "kernel/rtlil.h"
#include "kernel/register.h"
#include "kernel/sigtools.h"
#include "kernel/celltypes.h"
#include "kernel/cellaigs.h"
#include "kernel/log.h"
#include "yosys.pb.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct ProtobufDesignSerializer
{
	bool aig_mode_;
	bool use_selection_;
	yosys::pb::Design *pb_;

	Design *design_;
	Module *module_;

	SigMap sigmap_;
	int sigidcounter_;
	dict<SigBit, uint64_t> sigids_;
	pool<Aig> aig_models_;


	ProtobufDesignSerializer(bool use_selection, bool aig_mode) :
			aig_mode_(aig_mode), use_selection_(use_selection) { }

	string get_name(IdString name)
	{
		return RTLIL::unescape_id(name);
	}


	void serialize_parameters(google::protobuf::Map<std::string, yosys::pb::Parameter> *out,
		const dict<IdString, Const> &parameters)
	{
		for (auto &param : parameters) {
			std::string key = get_name(param.first);


			yosys::pb::Parameter pb_param;

			if ((param.second.flags & RTLIL::ConstFlags::CONST_FLAG_STRING) != 0) {
				pb_param.set_str(param.second.decode_string());
			} else if (GetSize(param.second.bits) > 64) {
				pb_param.set_str(param.second.as_string());
			} else {
				pb_param.set_int_(param.second.as_int());
			}

			(*out)[key] = pb_param;
		}
	}

	void get_bits(yosys::pb::BitVector *out, SigSpec sig)
	{
		for (auto bit : sigmap_(sig)) {
			auto sig = out->add_signal();

			// Constant driver.
			if (bit.wire == nullptr) {
				if (bit == State::S0) sig->set_constant(sig->CONSTANT_DRIVER_LOW);
				else if (bit == State::S1) sig->set_constant(sig->CONSTANT_DRIVER_HIGH);
				else if (bit == State::Sz) sig->set_constant(sig->CONSTANT_DRIVER_Z);
				else sig->set_constant(sig->CONSTANT_DRIVER_X);
				continue;
			}

			// Signal - give it a unique identifier.
			if (sigids_.count(bit) == 0) {
				sigids_[bit] = sigidcounter_++;
			}
			sig->set_id(sigids_[bit]);
		}
	}

	void serialize_module(yosys::pb::Module* out, Module *module)
	{
		module_ = module;
		log_assert(module_->design == design_);
		sigmap_.set(module_);
		sigids_.clear();
		sigidcounter_ = 0;

		serialize_parameters(out->mutable_attribute(), module_->attributes);

		for (auto n : module_->ports) {
			Wire *w = module->wire(n);
			if (use_selection_ && !module_->selected(w))
				continue;

			yosys::pb::Module::Port pb_port;
			pb_port.set_direction(w->port_input ? w->port_output ?
				yosys::pb::DIRECTION_INOUT : yosys::pb::DIRECTION_INPUT : yosys::pb::DIRECTION_OUTPUT);
			get_bits(pb_port.mutable_bits(), w);
			(*out->mutable_port())[get_name(n)] = pb_port;
		}

		for (auto c : module_->cells()) {
			if (use_selection_ && !module_->selected(c))
				continue;

			yosys::pb::Module::Cell pb_cell;
			pb_cell.set_hide_name(c->name[0] == '$');
			pb_cell.set_type(get_name(c->type));

			if (aig_mode_) {
				Aig aig(c);
				if (aig.name.empty())
					continue;
				pb_cell.set_model(aig.name);
				aig_models_.insert(aig);
			}
			serialize_parameters(pb_cell.mutable_parameter(), c->parameters);
			serialize_parameters(pb_cell.mutable_attribute(), c->attributes);

			if (c->known()) {
				for (auto &conn : c->connections()) {
					yosys::pb::Direction direction = yosys::pb::DIRECTION_OUTPUT;
					if (c->input(conn.first))
						direction = c->output(conn.first) ? yosys::pb::DIRECTION_INOUT : yosys::pb::DIRECTION_INPUT;
					(*pb_cell.mutable_port_direction())[get_name(conn.first)] = direction;
				}
			}
			for (auto &conn : c->connections()) {
				yosys::pb::BitVector vec;
				get_bits(&vec, conn.second);
				(*pb_cell.mutable_connection())[get_name(conn.first)] = vec;
			}

			(*out->mutable_cell())[get_name(c->name)] = pb_cell;
		}

		for (auto w : module_->wires()) {
			if (use_selection_ && !module_->selected(w))
				continue;

			auto netname = out->add_netname();
			netname->set_hide_name(w->name[0] == '$');
			get_bits(netname->mutable_bits(), w);
			serialize_parameters(netname->mutable_attributes(), w->attributes);
		}
	}


	void serialize_models(google::protobuf::Map<string, yosys::pb::Model> *models)
	{
		for (auto &aig : aig_models_) {
			yosys::pb::Model pb_model;
			for (auto &node : aig.nodes) {
				auto pb_node = pb_model.add_node();
				if (node.portbit >= 0) {
					if (node.inverter) {
						pb_node->set_type(pb_node->TYPE_NPORT);
					} else {
						pb_node->set_type(pb_node->TYPE_PORT);
					}
					auto port = pb_node->mutable_port();
					port->set_portname(log_id(node.portname));
					port->set_bitindex(node.portbit);
				} else if (node.left_parent < 0 && node.right_parent < 0) {
					if (node.inverter) {
						pb_node->set_type(pb_node->TYPE_TRUE);
					} else {
						pb_node->set_type(pb_node->TYPE_FALSE);
					}
				} else {
					if (node.inverter) {
						pb_node->set_type(pb_node->TYPE_NAND);
					} else {
						pb_node->set_type(pb_node->TYPE_AND);
					}
					auto gate = pb_node->mutable_gate();
					gate->set_left(node.left_parent);
					gate->set_right(node.right_parent);
				}
				for (auto &op : node.outports) {
					auto pb_op = pb_node->add_out_port();
					pb_op->set_name(log_id(op.first));
					pb_op->set_bit_index(op.second);
				}
			}
			(*models)[aig.name] = pb_model;
		}
	}

	void serialize_design(yosys::pb::Design *pb, Design *design)
	{
		GOOGLE_PROTOBUF_VERIFY_VERSION;
		pb_ = pb;
		pb_->Clear();
		pb_->set_creator(yosys_version_str);

		design_ = design;
		design_->sort();

		auto modules = use_selection_ ? design_->selected_modules() : design_->modules();
		for (auto mod : modules) {
			yosys::pb::Module pb_mod;
			serialize_module(&pb_mod, mod);
			(*pb->mutable_modules())[mod->name.str()] = pb_mod;
		}

		serialize_models(pb_->mutable_models());
	}
};

struct ProtobufBackend : public Backend {
	ProtobufBackend(): Backend("protobuf", "write design to a Protocol Buffer file") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    write_protobuf [options] [filename]\n");
		log("\n");
		log("Write a JSON netlist of the current design.\n");
		log("\n");
		log("    -aig\n");
		log("        include AIG models for the different gate types\n");
		log("\n");
		log("    -text\n");
		log("        output protobuf in Text/ASCII representation\n");
		log("\n");
		log("The schema of the output Protocol Buffer is defined in misc/yosys.pb in the\n");
		log("Yosys source code distribution.\n");
		log("\n");
	}
	void execute(std::ostream *&f, std::string filename, std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		bool aig_mode = false;
		bool text_mode = false;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-aig") {
				aig_mode = true;
				continue;
			}
			if (args[argidx] == "-text") {
				text_mode = true;
				continue;
			}
			break;
		}
		extra_args(f, filename, args, argidx, !text_mode);

		log_header(design, "Executing Protobuf backend.\n");

		yosys::pb::Design pb;
		ProtobufDesignSerializer serializer(false, aig_mode);
		serializer.serialize_design(&pb, design);

		if (text_mode) {
			string out;
			google::protobuf::TextFormat::PrintToString(pb, &out);
			*f << out;
		} else {
			pb.SerializeToOstream(f);
		}
	}
} ProtobufBackend;

struct ProtobufPass : public Pass {
	ProtobufPass() : Pass("protobuf", "write design in Protobuf format") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    protobuf [options] [selection]\n");
		log("\n");
		log("Write a JSON netlist of all selected objects.\n");
		log("\n");
		log("    -o <filename>\n");
		log("        write to the specified file.\n");
		log("\n");
		log("    -aig\n");
		log("        include AIG models for the different gate types\n");
		log("\n");
		log("    -text\n");
		log("        output protobuf in Text/ASCII representation\n");
		log("\n");
		log("The schema of the output Protocol Buffer is defined in misc/yosys.pb in the\n");
		log("Yosys source code distribution.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		std::string filename;
		bool aig_mode = false;
		bool text_mode = false;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-o" && argidx+1 < args.size()) {
				filename = args[++argidx];
				continue;
			}
			if (args[argidx] == "-aig") {
				aig_mode = true;
				continue;
			}
			if (args[argidx] == "-text") {
				text_mode = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		std::ostream *f;
		std::stringstream buf;

		if (!filename.empty()) {
			rewrite_filename(filename);
			std::ofstream *ff = new std::ofstream;
			ff->open(filename.c_str(), text_mode ? std::ofstream::trunc : (std::ofstream::trunc | std::ofstream::binary));
			if (ff->fail()) {
				delete ff;
				log_error("Can't open file `%s' for writing: %s\n", filename.c_str(), strerror(errno));
			}
			f = ff;
		} else {
			f = &buf;
		}

		yosys::pb::Design pb;
		ProtobufDesignSerializer serializer(true, aig_mode);
		serializer.serialize_design(&pb, design);

		if (text_mode) {
			string out;
			google::protobuf::TextFormat::PrintToString(pb, &out);
			*f << out;
		} else {
			pb.SerializeToOstream(f);
		}

		if (!filename.empty()) {
			delete f;
		} else {
			log("%s", buf.str().c_str());
		}
	}
} ProtobufPass;

PRIVATE_NAMESPACE_END;
