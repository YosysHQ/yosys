/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
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

#include "kernel/yosys.h"
#include "kernel/log.h"
#include <stdlib.h>
#include <string.h>

#include "frontends/verific/verific.h"
#include "frontends/verific/verific_command.h"

USING_YOSYS_NAMESPACE

#ifdef YOSYS_ENABLE_VERIFIC

#ifdef __clang__
#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Woverloaded-virtual"
#endif

#include "Array.h"
#include "RuntimeFlags.h"
#ifdef VERIFIC_HIER_TREE_SUPPORT
#include "hier_tree.h"
#endif

#ifdef VERIFIC_SYSTEMVERILOG_SUPPORT
#include "veri_file.h"
#include "VeriModule.h"
#include "VeriLibrary.h"
#include "VeriExpression.h"
#endif

#ifdef VERIFIC_VHDL_SUPPORT
#include "vhdl_file.h"
#include "VhdlIdDef.h"
#include "VhdlUnits.h"
#endif

#ifdef VERIFIC_EDIF_SUPPORT
#include "edif_file.h"
#endif

#ifdef VERIFIC_LIBERTY_SUPPORT
#include "synlib_file.h"
#endif

#include "VerificStream.h"
#include "FileSystem.h"

#ifdef YOSYSHQ_VERIFIC_EXTENSIONS
#include "VerificExtensions.h"
#endif

#ifndef YOSYSHQ_VERIFIC_API_VERSION
#warning "Only YosysHQ flavored Verific is fully supported. Please contact office@yosyshq.com for commercial support for Yosys+Verific."
#else
#if YOSYSHQ_VERIFIC_API_VERSION < 20230901
#  error "Please update your version of YosysHQ flavored Verific."
#endif
#endif

#if !defined(VERIFIC_VHDL_SUPPORT) && !defined(VERIFIC_SYSTEMVERILOG_SUPPORT)
#error "At least one of HDL languages must be enabled."
#endif

#ifdef __clang__
#pragma clang diagnostic pop
#endif

#ifdef VERIFIC_NAMESPACE
using namespace Verific;
#endif

#endif

#ifdef YOSYS_ENABLE_VERIFIC
YOSYS_NAMESPACE_BEGIN

// Verific use internally static data structures to keep current
// state, we can not mix new design with existing until current
// design is imported

void verific_cleanup();

void VerificSession::begin(Design *design)
{
	std::unique_lock<std::mutex> lock(mutex);
	while (owner != nullptr && owner != design)
		cv.wait(lock);
	owner = design;
}

std::unique_ptr<VerificSession> VerificSession::deferred_end(Design *design)
{
	std::lock_guard<std::mutex> lock(mutex);
	if (owner != design)
		return nullptr;
	return std::make_unique<VerificSession>();
}

VerificSession::~VerificSession()
{
	verific_cleanup();
	std::lock_guard<std::mutex> lock(mutex);
	owner = nullptr;
	cv.notify_all();
}

int verific_verbose;
bool verific_import_pending;
string verific_error_msg;
int verific_sva_fsm_limit;

const char *get_message_type(msg_type_t msg_type)
{
	switch (msg_type) {
	case VERIFIC_NONE:
		return "VERIFIC-NONE";
	case VERIFIC_ERROR:
		return "VERIFIC-ERROR";
	case VERIFIC_WARNING:
		return "VERIFIC-WARNING";
	case VERIFIC_IGNORE:
		return "VERIFIC-IGNORE";
	case VERIFIC_INFO:
		return "VERIFIC-INFO";
	case VERIFIC_COMMENT:
		return "VERIFIC-COMMENT";
	case VERIFIC_PROGRAM_ERROR:
		return "VERIFIC-PROGRAM_ERROR";
	default:
		return "VERIFIC-UNKNOWN";
	}
}

void msg_func(msg_type_t msg_type, const char *message_id, linefile_type linefile, const char *msg, va_list args)
{
	std::string id = message_id ? stringf("[%s] ",message_id) : "";
	string message = stringf("%s%s\n", id, vstringf(msg, args));
	auto src = !linefile ? LogSourceLocation{} : LogSourceLocation{LineFile::GetFileName(linefile),
#ifdef VERIFIC_LINEFILE_INCLUDES_COLUMNS
		int(linefile->GetLeftLine()), int(linefile->GetLeftCol()), int(linefile->GetRightLine()), int(linefile->GetRightCol())};
#else
		int(LineFile::GetLineNo(linefile))};
#endif

	if (log_verific_callback) {
		log_verific_callback(int(msg_type), message_id, src, message.c_str());
	} else {
		string message_prefix = stringf("%s: ",get_message_type(msg_type));
		if (msg_type == VERIFIC_ERROR || msg_type == VERIFIC_PROGRAM_ERROR) {
			logger().formatted_nonfatal_error(src, message_prefix, "%s%s\n", message);
		} else if (msg_type == VERIFIC_WARNING) {
			logger().formatted_warning(src, message_prefix, "%s%s\n", message);
		} else {
			logger().formatted_string(LogSeverity::Info, src, message_prefix, "%s%s\n", message);
		}
	}
	if (msg_type == VERIFIC_ERROR || msg_type == VERIFIC_PROGRAM_ERROR)
		verific_error_msg = "Design elaboration failed; see full log for details";
}

void set_verific_logging(void (*cb)(int msg_type, const char *message_id, LogSourceLocation src, const char *msg))
{
	Message::SetConsoleOutput(0);
	Message::RegisterCallBackMsg(msg_func);
	log_verific_callback = cb;
}

string get_full_netlist_name(Netlist *nl)
{
	if (nl->NumOfRefs() == 1) {
		Instance *inst = (Instance*)nl->GetReferences()->GetLast();
		return get_full_netlist_name(inst->Owner()) + "." + inst->Name();
	}

	return nl->CellBaseName();
}

#ifdef VERIFIC_SYSTEMVERILOG_SUPPORT
class YosysStreamCallBackHandler : public VerificStreamCallBackHandler
{
public:
	YosysStreamCallBackHandler() : VerificStreamCallBackHandler() { }
	virtual ~YosysStreamCallBackHandler() { }

	virtual verific_stream *GetSysCallStream(const char *file_path)
	{
		if (!file_path) return nullptr;

		linefile_type src_loc = GetFromLocation();

		char *this_file_name = nullptr;
		if (src_loc && !FileSystem::IsAbsolutePath(file_path)) {
			const char *src_file_name = LineFile::GetFileName(src_loc);
			char *dir_name = FileSystem::DirectoryPath(src_file_name);
			if (dir_name) {
				this_file_name = Strings::save(dir_name, "/", file_path);
				Strings::free(dir_name);
				file_path = this_file_name;
			}
		}
		verific_stream *strm = new verific_ifstream(file_path);
		Strings::free(this_file_name);
		return strm;
	}
};

YosysStreamCallBackHandler verific_read_cb;
#endif

#ifdef VERIFIC_SYSTEMVERILOG_SUPPORT
static msg_type_t prev_1063;
#endif
#ifdef VERIFIC_VHDL_SUPPORT
static msg_type_t prev_1240 ;
static msg_type_t prev_1241 ;
#endif
void save_blackbox_msg_state()
{
#ifdef VERIFIC_SYSTEMVERILOG_SUPPORT
	prev_1063 = Message::GetMessageType("VERI-1063") ;
	Message::SetMessageType("VERI-1063", VERIFIC_INFO);
#endif
#ifdef VERIFIC_VHDL_SUPPORT
	prev_1240 = Message::GetMessageType("VHDL-1240") ;
	prev_1241 = Message::GetMessageType("VHDL-1241") ;
	Message::SetMessageType("VHDL-1240", VERIFIC_INFO);
	Message::SetMessageType("VHDL-1241", VERIFIC_INFO);
#endif
}

void restore_blackbox_msg_state()
{
#ifdef VERIFIC_SYSTEMVERILOG_SUPPORT
	Message::ClearMessageType("VERI-1063") ;
	if (Message::GetMessageType("VERI-1063")!=prev_1063)
		Message::SetMessageType("VERI-1063", prev_1063);
#endif
#ifdef VERIFIC_VHDL_SUPPORT
	Message::ClearMessageType("VHDL-1240") ;
	Message::ClearMessageType("VHDL-1241") ;
	if (Message::GetMessageType("VHDL-1240")!=prev_1240)
		Message::SetMessageType("VHDL-1240", prev_1240);
	if (Message::GetMessageType("VHDL-1241")!=prev_1241)
		Message::SetMessageType("VHDL-1241", prev_1241);
#endif
}

void import_all(const char* work, std::map<std::string,Netlist*> *nl_todo, Map *parameters, bool show_message, std::string ppfile YS_MAYBE_UNUSED)
{
#ifdef YOSYSHQ_VERIFIC_EXTENSIONS
	save_blackbox_msg_state();
	VerificExtensions::ElaborateAndRewrite(work, parameters);
	verific_error_msg.clear();
	restore_blackbox_msg_state();
#endif
#ifdef VERIFIC_SYSTEMVERILOG_SUPPORT
	if (!ppfile.empty())
		veri_file::PrettyPrint(ppfile.c_str(), nullptr, work);
#endif

	Array vhdl_libs;
#ifdef VERIFIC_VHDL_SUPPORT
	VhdlLibrary *vhdl_lib = vhdl_file::GetLibrary(work, 1);
	if (vhdl_lib) vhdl_libs.InsertLast(vhdl_lib);
#endif
	Array veri_libs;
#ifdef VERIFIC_SYSTEMVERILOG_SUPPORT
	VeriLibrary *veri_lib = veri_file::GetLibrary(work, 1);
	if (veri_lib) veri_libs.InsertLast(veri_lib);
#endif

#ifdef VERIFIC_HIER_TREE_SUPPORT
	if (show_message)
		log("Running hier_tree::ElaborateAll().\n");
	Array *netlists = hier_tree::ElaborateAll(&veri_libs, &vhdl_libs, parameters);
	Netlist *nl;
	int i;

	FOREACH_ARRAY_ITEM(netlists, i, nl)
		nl_todo->emplace(nl->CellBaseName(), nl);
	delete netlists;
#else
	if (parameters->Size())
		log_warning("Please note that parameters are not propagated during import.\n");
#ifdef VERIFIC_SYSTEMVERILOG_SUPPORT
	if (show_message)
		log("Running veri_file::ElaborateAll().\n");
	veri_file::ElaborateAll(work);
#endif
#ifdef VERIFIC_VHDL_SUPPORT
	if (show_message)
		log("Running vhdl_file::ElaborateAll().\n");
	vhdl_file::ElaborateAll(work);
#endif
	MapIter mi ;
	Verific::Cell *c ;
	MapIter it ;
	Library *l ;
	FOREACH_LIBRARY_OF_LIBSET(Libset::Global(),it,l) {
		if (l == Library::Primitives() || l == Library::Operators()) continue;
		FOREACH_CELL_OF_LIBRARY(l,mi,c) {
			MapIter ni ;
			Netlist *nl;
			FOREACH_NETLIST_OF_CELL(c, ni, nl) {
				if (nl)
					nl_todo->emplace(nl->CellBaseName(), nl);
			}
		}
	}
#endif
}

std::set<std::string> import_tops(const char* work, std::map<std::string,Netlist*> *nl_todo, Map *parameters, bool show_message, std::string ppfile YS_MAYBE_UNUSED, std::vector<std::string> &tops, std::string *top)
{
	std::set<std::string> top_mod_names;
	Array *netlists = nullptr;
	(void)top;

#ifdef VERIFIC_VHDL_SUPPORT
	VhdlLibrary *vhdl_lib = vhdl_file::GetLibrary(work, 1);
#endif
#ifdef VERIFIC_SYSTEMVERILOG_SUPPORT
	VeriLibrary* veri_lib = veri_file::GetLibrary(work, 1);
#endif

#ifdef YOSYSHQ_VERIFIC_EXTENSIONS
	for (int static_elaborate = 1; static_elaborate >= 0; static_elaborate--)
#endif
	{
		Array vhdl_units;
		Array veri_modules;
		for (std::string n : tops)
		{
			const char *name = n.c_str();
			top_mod_names.insert(name);

#ifdef VERIFIC_SYSTEMVERILOG_SUPPORT
			VeriModule *veri_module = veri_lib ? veri_lib->GetModule(name, 1) : nullptr;
			if (veri_module) {
				if (veri_module->IsConfiguration()) {
					if (show_message)
						log("Adding Verilog configuration '%s' to elaboration queue.\n", name);
					veri_modules.InsertLast(veri_module);
					top_mod_names.erase(name);
					VeriConfiguration *cfg = (VeriConfiguration*)veri_module;
					VeriName *module_name;
					int i;
					FOREACH_ARRAY_ITEM(cfg->GetTopModuleNames(), i, module_name) {
						VeriLibrary *lib = veri_module->GetLibrary() ;
						if (module_name && module_name->IsHierName()) {
							VeriName *prefix = module_name->GetPrefix() ;
							const char *lib_name = (prefix) ? prefix->GetName() : 0 ;
							if (work != lib_name) lib = veri_file::GetLibrary(lib_name, 1) ;
						}
						if (lib && module_name)
							top_mod_names.insert(lib->GetModule(module_name->GetName(), 1)->GetName());
					}
				} else {
					if (show_message)
						log("Adding Verilog module '%s' to elaboration queue.\n", name);
					veri_modules.InsertLast(veri_module);
				}
			continue;
			}
#endif
#ifdef VERIFIC_VHDL_SUPPORT
			VhdlDesignUnit *vhdl_unit = vhdl_lib ? vhdl_lib->GetPrimUnit(name) : nullptr;
			if (vhdl_unit) {
				if (show_message)
					log("Adding VHDL unit '%s' to elaboration queue.\n", name);
				vhdl_units.InsertLast(vhdl_unit);
				if (strcmp(name, vhdl_unit->Id()->OrigName()) != 0) {
					top_mod_names.erase(name);
					top_mod_names.insert(vhdl_unit->Id()->OrigName());
					if (top && *top == name)
						*top = vhdl_unit->Id()->OrigName();
				}
				continue;
			}
#endif
			log_error("Can't find module/unit '%s'.\n", name);
		}

#ifdef YOSYSHQ_VERIFIC_EXTENSIONS
		if (static_elaborate) {
			save_blackbox_msg_state();
			VerificExtensions::ElaborateAndRewrite(work, &veri_modules, &vhdl_units, parameters);
			verific_error_msg.clear();
			restore_blackbox_msg_state();
#endif
#ifdef VERIFIC_SYSTEMVERILOG_SUPPORT
			if (!ppfile.empty())
				veri_file::PrettyPrint(ppfile.c_str(), nullptr, work);
#endif
#ifdef YOSYSHQ_VERIFIC_EXTENSIONS
			continue;
		}
#endif
#ifdef VERIFIC_SYSTEMVERILOG_SUPPORT
		const char *lib_name = nullptr;
		SetIter si;
		FOREACH_SET_ITEM(veri_file::GetAllLOptions(), si, &lib_name) {
			VeriLibrary* veri_lib = veri_file::GetLibrary(lib_name, 0);
			if (veri_lib) {
				// Also elaborate all root modules since they may contain bind statements
				MapIter mi;
				VeriModule *veri_module;
				FOREACH_VERILOG_MODULE_IN_LIBRARY(veri_lib, mi, veri_module) {
					if (!veri_module->IsRootModule()) continue;
					veri_modules.InsertLast(veri_module);
				}
			}
		}
#endif
#ifdef VERIFIC_HIER_TREE_SUPPORT
		if (show_message)
			log("Running hier_tree::Elaborate().\n");
		netlists = hier_tree::Elaborate(&veri_modules, &vhdl_units, parameters);
#else
#if defined(VERIFIC_SYSTEMVERILOG_SUPPORT) && !defined(VERIFIC_VHDL_SUPPORT)
		if (show_message)
			log("Running veri_file::ElaborateMultipleTop().\n");
		// SystemVerilog support only
		netlists = veri_file::ElaborateMultipleTop(&veri_modules, parameters);
#elif defined(VERIFIC_VHDL_SUPPORT) && !defined(VERIFIC_SYSTEMVERILOG_SUPPORT)
		if (show_message)
			log("Running vhdl_file::Elaborate().\n");
		// VHDL support	only
		netlists = new Array(top_mod_names.size());
		for (auto &name : top_mod_names) {
			vhdl_file::Elaborate(name.c_str(), work, 0, parameters);
			netlists->InsertLast(Netlist::PresentDesign());
		}
#elif defined(VERIFIC_SYSTEMVERILOG_SUPPORT) && defined(VERIFIC_VHDL_SUPPORT)
		// Both SystemVerilog and VHDL support
		if (veri_modules.Size()>0) {
			if (show_message)
				log("Running veri_file::ElaborateMultipleTop().\n");
			netlists = veri_file::ElaborateMultipleTop(&veri_modules, parameters);
		} else
			netlists = new Array(1);
		if (vhdl_units.Size()>0) {
			if (show_message)
				log("Running vhdl_file::Elaborate().\n");
			for (auto &name : top_mod_names) {
				vhdl_file::Elaborate(name.c_str(), work, 0, parameters);
				netlists->InsertLast(Netlist::PresentDesign());
			}
		}
#else
#endif
#endif
	}
	Netlist *nl;
	int i;

	FOREACH_ARRAY_ITEM(netlists, i, nl) {
		if (!nl) continue;
		if (!top_mod_names.count(nl->CellBaseName()))
			continue;
		nl->AddAtt(new Att(" \\top", NULL));
		nl_todo->emplace(nl->CellBaseName(), nl);
	}
	delete netlists;
	return top_mod_names;
}

static bool set_verific_global_flags = true;

static void set_global_flags()
{
	if (!set_verific_global_flags)
		return;

	Message::SetConsoleOutput(0);
	Message::RegisterCallBackMsg(msg_func);

	RuntimeFlags::SetVar("db_preserve_user_instances", 1);
	RuntimeFlags::SetVar("db_preserve_user_nets", 1);
	RuntimeFlags::SetVar("db_preserve_x", 1);

	RuntimeFlags::SetVar("db_allow_external_nets", 1);
	RuntimeFlags::SetVar("db_infer_wide_operators", 1);
	RuntimeFlags::SetVar("db_infer_set_reset_registers", 0);

	// Properly respect order of read and write for rams
	RuntimeFlags::SetVar("db_change_inplace_ram_blocking_write_before_read", 1);

#ifdef VERIFIC_SYSTEMVERILOG_SUPPORT
	RuntimeFlags::SetVar("veri_extract_dualport_rams", 0);
	RuntimeFlags::SetVar("veri_extract_multiport_rams", 1);
	RuntimeFlags::SetVar("veri_allow_any_ram_in_loop", 1);
	RuntimeFlags::SetVar("veri_replace_const_exprs", 1);
#endif
#ifdef VERIFIC_VHDL_SUPPORT
	RuntimeFlags::SetVar("vhdl_extract_dualport_rams", 0);
	RuntimeFlags::SetVar("vhdl_extract_multiport_rams", 1);
	RuntimeFlags::SetVar("vhdl_allow_any_ram_in_loop", 1);
	RuntimeFlags::SetVar("vhdl_replace_const_exprs", 1);

	RuntimeFlags::SetVar("vhdl_support_variable_slice", 1);
	RuntimeFlags::SetVar("vhdl_ignore_assertion_statements", 0);

	RuntimeFlags::SetVar("vhdl_preserve_assignments", 1);
	//RuntimeFlags::SetVar("vhdl_preserve_comments", 1);
	RuntimeFlags::SetVar("vhdl_preserve_drivers", 1);
#endif
#ifdef VERIFIC_SYSTEMVERILOG_SUPPORT
	RuntimeFlags::SetVar("veri_preserve_assignments", 1);
	RuntimeFlags::SetVar("veri_preserve_comments", 1);
	RuntimeFlags::SetVar("veri_preserve_drivers", 1);

	// Workaround for VIPER #13851
	RuntimeFlags::SetVar("veri_create_name_for_unnamed_gen_block", 1);

	// WARNING: instantiating unknown module 'XYZ' (VERI-1063)
	Message::SetMessageType("VERI-1063", VERIFIC_ERROR);

	// Downgrade warnings about things that are normal
	// VERIFIC-WARNING [VERI-1209] foo.sv:98: expression size 7 truncated to fit in target size 6
	Message::SetMessageType("VERI-1209", VERIFIC_INFO);
	// VERIFIC-WARNING [VERI-1142] foo.sv:55: system task 'display' is ignored for synthesis
	Message::SetMessageType("VERI-1142", VERIFIC_INFO);
	// VERIFIC-WARNING [VERI-2418] foo.svh:503: parameter 'all_cfgs_gp' declared inside package 'bp_common_pkg' shall be treated as localparam
	Message::SetMessageType("VERI-2418", VERIFIC_INFO);

	// https://github.com/YosysHQ/yosys/issues/1055
	RuntimeFlags::SetVar("veri_elaborate_top_level_modules_having_interface_ports", 1) ;
#endif
	RuntimeFlags::SetVar("verific_produce_verbose_syntax_error_message", 1);

#ifndef DB_PRESERVE_INITIAL_VALUE
#  warning Verific was built without DB_PRESERVE_INITIAL_VALUE.
#endif

	set_verific_global_flags = false;
}

void verific_setup()
{
	set_global_flags();
#ifdef VERIFIC_SYSTEMVERILOG_SUPPORT
	veri_file::RegisterCallBackVerificStream(&verific_read_cb);
#endif
}

void verific_cleanup()
{
#ifdef YOSYSHQ_VERIFIC_EXTENSIONS
	VerificExtensions::Reset();
#endif
#ifdef VERIFIC_HIER_TREE_SUPPORT
	hier_tree::DeleteHierarchicalTree();
#endif
#ifdef VERIFIC_SYSTEMVERILOG_SUPPORT
	veri_file::Reset();
#endif
#ifdef VERIFIC_VHDL_SUPPORT
	vhdl_file::Reset();
#endif
#ifdef VERIFIC_EDIF_SUPPORT
	edif_file::Reset();
#endif
#ifdef VERIFIC_LIBERTY_SUPPORT
	synlib_file::Reset();
#endif
	Libset::Reset();
	Message::Reset();
	RuntimeFlags::DeleteAllFlags();
	set_verific_global_flags = true;
	LineFile::DeleteAllLineFiles();
	VerificCommand::reset_settings();
	verific_import_pending = false;
}

std::string verific_import(Design *design, const std::map<std::string,std::string> &parameters, std::string top)
{
	verific_sva_fsm_limit = 16;

	std::map<std::string,Netlist*> nl_todo, nl_done;

	Map verific_params(STRING_HASH);
	for (const auto &i : parameters)
		verific_params.Insert(i.first.c_str(), i.second.c_str());

	std::set<std::string> top_mod_names;
	if (top.empty()) {
		import_all("work", &nl_todo, &verific_params, false, "");
	} else {
		std::vector<std::string> tops;
		tops.push_back(top);
#ifdef VERIFIC_SYSTEMVERILOG_SUPPORT
		veri_file::RemoveAllLOptions();
		veri_file::AddLOption("work");
#endif
		top_mod_names = import_tops("work", &nl_todo, &verific_params, false, "", tops, &top) ;
	}

	if (!verific_error_msg.empty())
		log_error("%s\n", verific_error_msg);

	for (auto nl : nl_todo)
		nl.second->ChangePortBusStructures(1 /* hierarchical */);

	verific_extnets(nl_todo);

	while (!nl_todo.empty()) {
		auto it = nl_todo.begin();
		Netlist *nl = it->second;
		if (nl_done.count(it->first) == 0) {
			VerificImporter importer(false, false, false, false, false, false, false, false);
			nl_done[it->first] = it->second;
			importer.import_netlist(design, nl, nl_todo, top_mod_names.count(nl->CellBaseName()));
		}
		nl_todo.erase(it);
	}

	if (!verific_error_msg.empty())
		log_error("%s\n", verific_error_msg);
	return top;
}

bool check_noverific_env()
{
	const char *e = getenv("YOSYS_NOVERIFIC");
	if (e == nullptr)
		return false;
	if (atoi(e) == 0)
		return false;
	return true;
}

YOSYS_NAMESPACE_END
#endif /* YOSYS_ENABLE_VERIFIC */
