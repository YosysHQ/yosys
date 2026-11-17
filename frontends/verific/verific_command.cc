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
#include <filesystem>

#include "frontends/verific/verific_command.h"

#ifdef __clang__
#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Woverloaded-virtual"
#endif

#include "Array.h"
#include "RuntimeFlags.h"

#ifdef VERIFIC_SYSTEMVERILOG_SUPPORT
#include "veri_file.h"
#include "VeriModule.h"
#include "VeriWrite.h"
#include "VeriLibrary.h"
#endif

#ifdef VERIFIC_VHDL_SUPPORT
#include "vhdl_file.h"
#include "VhdlUnits.h"
#endif

#ifdef VERIFIC_EDIF_SUPPORT
#include "edif_file.h"
#endif

#ifdef VERIFIC_LIBERTY_SUPPORT
#include "synlib_file.h"
#include "SynlibGroup.h"
#endif

#ifdef YOSYSHQ_VERIFIC_EXTENSIONS
#include "VerificExtensions.h"
#endif

#ifdef __clang__
#pragma clang diagnostic pop
#endif

#ifdef VERIFIC_NAMESPACE
using namespace Verific;
#endif

YOSYS_NAMESPACE_BEGIN

static bool already_imported = false;

#ifdef VERIFIC_SYSTEMVERILOG_SUPPORT
static std::vector<std::string> verific_incdirs, verific_libdirs, verific_libexts;
#endif

void VerificCommand::reset_settings()
{
#ifdef VERIFIC_SYSTEMVERILOG_SUPPORT
	verific_incdirs.clear();
	verific_libdirs.clear();
	verific_libexts.clear();
#endif
}

VerificCommand::VerificCommand(Pass &pass, std::vector<std::string> &args, RTLIL::Design *design) : pass(pass), args(args), design(design)
{
	for (; argidx < GetSize(args); argidx++)
	{
		if (args[argidx] == "-work" && argidx+1 < GetSize(args)) {
			work = args[++argidx];
			is_work_set = true;
			continue;
		}
#ifdef VERIFIC_SYSTEMVERILOG_SUPPORT
		if (args[argidx] == "-L" && argidx+1 < GetSize(args)) {
			search_libraries.push_back(args[++argidx]);
			continue;
		}
#endif
		break;
	}

	if (argidx < GetSize(args))
		mode = args[argidx];
}

VerificCommand::~VerificCommand()
{
	if (tmp_files.empty())
		return;
	log("Removing temp files.\n");
	for (auto &fn : tmp_files)
		remove(fn.c_str());
}

void VerificCommand::apply_library_options()
{
#ifdef VERIFIC_SYSTEMVERILOG_SUPPORT
	veri_file::RemoveAllLOptions();
	if (std::find(search_libraries.begin(), search_libraries.end(), work) == search_libraries.end())
		veri_file::AddLOption(work.c_str());
	for (auto &library : search_libraries)
		veri_file::AddLOption(library.c_str());
#endif
}

bool VerificCommand::change_setting()
{
	if (mode == "-set-error" || mode == "-set-warning" || mode == "-set-info" || mode == "-set-ignore")
		set_msg_type();
#ifdef VERIFIC_SYSTEMVERILOG_SUPPORT
	else if (mode == "-vlog-incdir")
		append_remaining_args(verific_incdirs);
	else if (mode == "-vlog-libdir")
		append_remaining_args(verific_libdirs);
	else if (mode == "-vlog-libext")
		append_remaining_args(verific_libexts);
	else if (mode == "-vlog-define")
		define_macros();
	else if (mode == "-vlog-undef")
		undefine_macros();
#endif
	else
		return false;
	return true;
}

void VerificCommand::run()
{
	if (change_setting())
		return;

	apply_library_options();

	if (mode == "-import")
		import_design();
#ifdef VERIFIC_SYSTEMVERILOG_SUPPORT
	else if (mode == "-target")
		read_target();
	else if (mode == "-f" || mode == "-F")
		read_f_file();
	else if (const VerilogStandard *verilog = find_verilog_standard(mode))
		read_verilog(*verilog);
#endif
#ifdef VERIFIC_VHDL_SUPPORT
	else if (const VhdlStandard *vhdl = find_vhdl_standard(mode))
		read_vhdl(*vhdl);
#endif
#ifdef VERIFIC_EDIF_SUPPORT
	else if (mode == "-edif")
		read_edif();
#endif
#ifdef VERIFIC_LIBERTY_SUPPORT
	else if (mode == "-liberty")
		read_liberty();
#endif
	else if (mode == "-pp")
		pretty_print();
	else if (mode == "-cfg")
		configure();
	else
		run_extension();
}

std::string VerificCommand::frontend_rewrite()
{
	std::string filename = args[argidx++];
	//Accommodate heredocs with EOT marker spaced out from "<<", e.g. "<< EOT" vs. "<<EOT"
	if (filename == "<<" && (argidx < GetSize(args))) {
		filename += args[argidx++];
	}
	if (filename.compare(0, 2, "<<") == 0) {
		if (filename.size() <= 2)
			log_error("Missing EOT marker in here document!\n");
		std::string eot_marker = filename.substr(2);
		if (Frontend::current_script_file == nullptr)
			filename = "<stdin>";
		std::string last_here_document;
		while (1) {
			std::string buffer;
			char block[4096];
			while (1) {
				if (fgets(block, 4096, Frontend::current_script_file == nullptr? stdin : Frontend::current_script_file) == nullptr)
					log_error("Unexpected end of file in here document '%s'!\n", filename);
				buffer += block;
				if (buffer.size() > 0 && (buffer[buffer.size() - 1] == '\n' || buffer[buffer.size() - 1] == '\r'))
					break;
			}
			size_t indent = buffer.find_first_not_of(" \t\r\n");
			if (indent != std::string::npos && buffer.compare(indent, eot_marker.size(), eot_marker) == 0)
				break;
			last_here_document += buffer;
		}
		filename = make_temp_file();
		tmp_files.push_back(filename);
		std::ofstream file(filename);
		file << last_here_document;
	} else {
		rewrite_filename(filename);
	}
	return filename;
}


#ifdef VERIFIC_VHDL_SUPPORT
static void add_units_to_map(Map &map, std::string work, bool flag_lib)
{
	MapIter mi ;
	VhdlPrimaryUnit *unit ;
	if (!flag_lib) return;
	VhdlLibrary *vhdl_lib = vhdl_file::GetLibrary(work.c_str(), 1);
	if (vhdl_lib) {
		FOREACH_VHDL_PRIMARY_UNIT(vhdl_lib, mi, unit) {
			if (!unit) continue;
			map.Insert(unit,unit);
		}
	}
	save_blackbox_msg_state();
}

static void set_units_to_blackbox(Map &map, std::string work, bool flag_lib)
{
	MapIter mi ;
	VhdlPrimaryUnit *unit ;
	if (!flag_lib) return;
	VhdlLibrary *vhdl_lib = vhdl_file::GetLibrary(work.c_str(), 1);
	FOREACH_VHDL_PRIMARY_UNIT(vhdl_lib, mi, unit) {
		if (!unit) continue;
		if (!map.GetValue(unit)) {
			unit->SetCompileAsBlackbox();
		}
	}
	restore_blackbox_msg_state();
}
#endif

#ifdef VERIFIC_SYSTEMVERILOG_SUPPORT
static void add_modules_to_map(Map &map, std::string work, bool flag_lib)
{
	MapIter mi ;
	VeriModule *veri_module ;
	if (!flag_lib) return;
	VeriLibrary *veri_lib = veri_file::GetLibrary(work.c_str(), 1);
	if (veri_lib) {
		FOREACH_VERILOG_MODULE_IN_LIBRARY(veri_lib, mi, veri_module) {
			if (!veri_module) continue;
			map.Insert(veri_module,veri_module);
		}
	}
	save_blackbox_msg_state();
}

static void set_modules_to_blackbox(Map &map, std::string work, bool flag_lib)
{
	MapIter mi ;
	VeriModule *veri_module ;
	if (!flag_lib) return;
	VeriLibrary *veri_lib = veri_file::GetLibrary(work.c_str(), 1);
	FOREACH_VERILOG_MODULE_IN_LIBRARY(veri_lib, mi, veri_module) {
		if (!veri_module) continue;
		if (!map.GetValue(veri_module)) {
			veri_module->SetCompileAsBlackbox();
		}
	}
	restore_blackbox_msg_state();
}
#endif

#ifdef VERIFIC_SYSTEMVERILOG_SUPPORT
struct VerificCommand::VerilogStandard {
	const char *flag;
	unsigned mode;
};

const VerificCommand::VerilogStandard *VerificCommand::find_verilog_standard(const std::string &flag)
{
	static const VerilogStandard standards[] = {
		{"-vlog95", veri_file::VERILOG_95},
		{"-vlog2k", veri_file::VERILOG_2K},
		{"-sv2005", veri_file::SYSTEM_VERILOG_2005},
		{"-sv2009", veri_file::SYSTEM_VERILOG_2009},
		{"-sv2012", veri_file::SYSTEM_VERILOG_2012},
		{"-sv2017", veri_file::SYSTEM_VERILOG_2017},
		{"-sv2023", veri_file::SYSTEM_VERILOG_2023},
		{"-sv", veri_file::SYSTEM_VERILOG},
		{"-formal", veri_file::SYSTEM_VERILOG},
	};
	for (auto &standard : standards)
		if (flag == standard.flag)
			return &standard;
	return nullptr;
}

static void analyze_verilog_files(Array &file_names, unsigned verilog_mode, const std::string &work, bool flag_lib)
{
	Map map(POINTER_HASH);
	add_modules_to_map(map, work, flag_lib);
	if (!veri_file::AnalyzeMultipleFiles(&file_names, verilog_mode, work.c_str(), veri_file::MFCU)) {
		verific_error_msg.clear();
		log_cmd_error("Reading Verilog/SystemVerilog sources failed.\n");
	}
	char* fn;
	int i = 0;

	FOREACH_ARRAY_ITEM(&file_names, i, fn) {
		free(fn);
	}
	set_modules_to_blackbox(map, work, flag_lib);
	verific_import_pending = true;
}
#endif

#ifdef VERIFIC_VHDL_SUPPORT
struct VerificCommand::VhdlStandard {
	const char *flag;
	unsigned mode;
	const char *name;
	const char *library_dir;

	void set_library_path() const
	{
		vhdl_file::SetDefaultLibraryPath((proc_share_dirname() + library_dir).c_str());
	}
};

const VerificCommand::VhdlStandard *VerificCommand::find_vhdl_standard(const std::string &flag)
{
	static const VhdlStandard standards[] = {
		{"-vhdl87", vhdl_file::VHDL_87, "VHDL_87", "verific/vhdl_vdbs_1987"},
		{"-vhdl93", vhdl_file::VHDL_93, "VHDL_93", "verific/vhdl_vdbs_1993"},
		{"-vhdl2k", vhdl_file::VHDL_2K, "VHDL_2K", "verific/vhdl_vdbs_1993"},
		{"-vhdl2008", vhdl_file::VHDL_2008, "VHDL_2008", "verific/vhdl_vdbs_2008"},
		{"-vhdl2019", vhdl_file::VHDL_2019, "VHDL_2019", "verific/vhdl_vdbs_2019"},
		{"-vhdl", vhdl_file::VHDL_2008, "VHDL_2008", "verific/vhdl_vdbs_2008"},
	};
	for (auto &standard : standards)
		if (flag == standard.flag)
			return &standard;
	return nullptr;
}
#endif

void VerificCommand::set_msg_type()
{
	msg_type_t new_type;

	if (mode == "-set-error")
		new_type = VERIFIC_ERROR;
	else if (mode == "-set-warning")
		new_type = VERIFIC_WARNING;
	else if (mode == "-set-info")
		new_type = VERIFIC_INFO;
	else if (mode == "-set-ignore")
		new_type = VERIFIC_IGNORE;
	else
		log_abort();

	for (argidx++; argidx < GetSize(args); argidx++) {
		if (Strings::compare(args[argidx].c_str(), "errors")) {
			Message::SetMessageType("VERI-1063", new_type);
			Message::SetAllMessageType(VERIFIC_ERROR, new_type);
		} else if (Strings::compare(args[argidx].c_str(), "warnings")) {
			Message::SetAllMessageType(VERIFIC_WARNING, new_type);
		} else if (Strings::compare(args[argidx].c_str(), "infos")) {
			Message::SetMessageType("VERI-1209", new_type);
			Message::SetMessageType("VERI-1142", new_type);
			Message::SetMessageType("VERI-2418", new_type);
			Message::SetAllMessageType(VERIFIC_INFO, new_type);
		} else if (Strings::compare(args[argidx].c_str(), "comments")) {
			Message::SetAllMessageType(VERIFIC_COMMENT, new_type);
		} else {
			Message::SetMessageType(args[argidx].c_str(), new_type);
		}
	}
}

#ifdef VERIFIC_SYSTEMVERILOG_SUPPORT
void VerificCommand::append_remaining_args(std::vector<std::string> &list)
{
	for (argidx++; argidx < GetSize(args); argidx++)
		list.push_back(args[argidx]);
}

void VerificCommand::define_macros()
{
	for (argidx++; argidx < GetSize(args); argidx++) {
		string name = args[argidx];
		size_t equal = name.find('=');
		if (equal != std::string::npos) {
			string value = name.substr(equal+1);
			name = name.substr(0, equal);
			veri_file::DefineCmdLineMacro(name.c_str(), value.c_str());
		} else {
			veri_file::DefineCmdLineMacro(name.c_str());
		}
	}
}

void VerificCommand::undefine_macros()
{
	for (argidx++; argidx < GetSize(args); argidx++) {
		string name = args[argidx];
		veri_file::UndefineMacro(name.c_str());
	}
}

void VerificCommand::read_target()
{
	argidx++;
	log_experimental("verific -target");

	if (argidx >= GetSize(args))
		log_cmd_error("Missing target for `-target'.\n");

	std::string synth_target = args[argidx++];
	std::string synth_family;

	if (argidx < GetSize(args) && args[argidx] == "-family") {
		argidx++;
		log_experimental("verific -family");

		if (argidx >= GetSize(args))
			log_cmd_error("Missing family for `-family'.\n");

		synth_family = args[argidx++];
	} else if (argidx < GetSize(args) && args[argidx][0] == '-') {
		log_cmd_error("Unknown option `%s'.\n", args[argidx]);
	}
	auto target_it = target_register.find(synth_target);
	if (target_it == target_register.end())
		log_cmd_error("Unknown target '%s'.\n", synth_target);

	auto family_it = target_it->second.families.find(synth_family);
	if (family_it == target_it->second.families.end()) {
		if (synth_family.empty())
			log_cmd_error("Family must be specified for target '%s'.\n", synth_target);
		else
			log_cmd_error("Unknown family '%s' for target '%s'.\n",
					synth_family, synth_target);
	}

	bool flag_lib = true;
	Array file_names;
	unsigned verilog_mode = veri_file::SYSTEM_VERILOG;
	veri_file::DefineMacro("YOSYS");
	veri_file::DefineMacro("VERIFIC");

	for (auto &file : family_it->second.files) {
		rewrite_filename(file);
		file_names.Insert(strdup(file.c_str()));
		std::string dir = std::filesystem::path(file).parent_path().string();
		veri_file::AddIncludeDir(dir.c_str());
	}

	analyze_verilog_files(file_names, verilog_mode, work, flag_lib);
}

void VerificCommand::read_f_file()
{
	unsigned verilog_mode = veri_file::UNDEFINED;
#ifdef VERIFIC_VHDL_SUPPORT
	unsigned vhdl_mode = vhdl_file::UNDEFINED;
#endif
	bool is_formal = false;
	const char* filename = nullptr;

	Verific::veri_file::f_file_flags flags = (args[argidx] == "-f") ? veri_file::F_FILE_NONE : veri_file::F_FILE_CAPITAL;

	for (argidx++; argidx < GetSize(args); argidx++) {
		if (const VerilogStandard *verilog = find_verilog_standard(args[argidx])) {
			verilog_mode = verilog->mode;
			if (args[argidx] == "-formal") is_formal = true;
			continue;
		}
#ifdef VERIFIC_VHDL_SUPPORT
		if (const VhdlStandard *vhdl = find_vhdl_standard(args[argidx])) {
			vhdl_mode = vhdl->mode;
			vhdl->set_library_path();
			continue;
		}
#endif
		if (args[argidx].compare(0, 1, "-") == 0)
			pass.cmd_error(args, argidx, "unknown option");

		if (filename)
			log_cmd_error("Only one filename can be specified.\n");
		filename = args[argidx].c_str();
	}
	if (!filename)
		log_cmd_error("Filename must be specified.\n");

	unsigned analysis_mode = verilog_mode; // keep default as provided by user if not defined in file
	Array *file_names = veri_file::ProcessFFile(filename, flags, analysis_mode);
	if (analysis_mode != verilog_mode)
		log_warning("Provided verilog mode differs from one specified in file.\n");

	veri_file::DefineMacro("YOSYS");
	veri_file::DefineMacro("VERIFIC");
	veri_file::DefineMacro(is_formal ? "FORMAL" : "SYNTHESIS");

#ifdef VERIFIC_VHDL_SUPPORT
	if (vhdl_mode == vhdl_file::UNDEFINED) {
		vhdl_file::SetDefaultLibraryPath((proc_share_dirname() + "verific/vhdl_vdbs_2008").c_str());
		vhdl_mode = vhdl_file::VHDL_2008;
	}
	int i;
	Array *file_names_sv = new Array(POINTER_HASH);
	FOREACH_ARRAY_ITEM(file_names, i, filename) {
		std::string filename_str = filename;
		if ((filename_str.substr(filename_str.find_last_of(".") + 1) == "vhd") ||
				(filename_str.substr(filename_str.find_last_of(".") + 1) == "vhdl")) {
			if (!vhdl_file::Analyze(filename, work.c_str(), vhdl_mode)) {
				verific_error_msg.clear();
				log_cmd_error("Reading VHDL sources failed.\n");
			}
		} else {
			file_names_sv->Insert(strdup(filename));
		}
	}
	if (!veri_file::AnalyzeMultipleFiles(file_names_sv, analysis_mode, work.c_str(), veri_file::MFCU)) {
		verific_error_msg.clear();
		log_cmd_error("Reading Verilog/SystemVerilog sources failed.\n");
	}
	delete file_names_sv;
#else
	if (!veri_file::AnalyzeMultipleFiles(file_names, analysis_mode, work.c_str(), veri_file::MFCU)) {
		verific_error_msg.clear();
		log_cmd_error("Reading Verilog/SystemVerilog sources failed.\n");
	}
#endif

	delete file_names;
	verific_import_pending = true;
}

void VerificCommand::read_verilog(const VerilogStandard &standard)
{
	Array file_names;
	unsigned verilog_mode = standard.mode;

	veri_file::DefineMacro("YOSYS");
	veri_file::DefineMacro("VERIFIC");
	veri_file::DefineMacro(args[argidx] == "-formal" ? "FORMAL" : "SYNTHESIS");

	for (argidx++; argidx < GetSize(args) && GetSize(args[argidx]) >= 2 && args[argidx].compare(0, 2, "-D") == 0; argidx++) {
		std::string name = args[argidx].substr(2);
		if (args[argidx] == "-D") {
			if (++argidx >= GetSize(args))
				break;
			name = args[argidx];
		}
		size_t equal = name.find('=');
		if (equal != std::string::npos) {
			string value = name.substr(equal+1);
			name = name.substr(0, equal);
			veri_file::DefineMacro(name.c_str(), value.c_str());
		} else {
			veri_file::DefineMacro(name.c_str());
		}
	}

	for (auto &dir : verific_incdirs)
		veri_file::AddIncludeDir(dir.c_str());
	for (auto &dir : verific_libdirs)
		veri_file::AddYDir(dir.c_str());
	for (auto &ext : verific_libexts)
		veri_file::AddLibExt(ext.c_str());

	bool flag_lib = false;
	while (argidx < GetSize(args)) {
		if (args[argidx] == "-lib") {
			flag_lib = true;
			argidx++;
			continue;
		}
		if (args[argidx].compare(0, 1, "-") == 0) {
			pass.cmd_error(args, argidx, "unknown option");
			return;
		}
		std::string filename = frontend_rewrite();
		file_names.Insert(strdup(filename.c_str()));
	}
	analyze_verilog_files(file_names, verilog_mode, work, flag_lib);
}
#endif

#ifdef VERIFIC_VHDL_SUPPORT
void VerificCommand::read_vhdl(const VhdlStandard &standard)
{
	standard.set_library_path();
	argidx++;
	bool flag_lib = false;
	while (argidx < GetSize(args)) {
		if (args[argidx] == "-lib") {
			flag_lib = true;
			argidx++;
			continue;
		}
		if (args[argidx].compare(0, 1, "-") == 0)
			pass.cmd_error(args, argidx, "unknown option");
		Map map(POINTER_HASH);
		add_units_to_map(map, work, flag_lib);
		std::string filename = frontend_rewrite();
		if (!vhdl_file::Analyze(filename.c_str(), work.c_str(), standard.mode))
			log_cmd_error("Reading `%s' in %s mode failed.\n", filename, standard.name);
		set_units_to_blackbox(map, work, flag_lib);
	}
	verific_import_pending = true;
}
#endif

#ifdef VERIFIC_EDIF_SUPPORT
void VerificCommand::read_edif()
{
	edif_file edif;
	argidx++;
	while (argidx < GetSize(args)) {
		std::string filename = frontend_rewrite();
		if (!edif.Read(filename.c_str()))
			log_cmd_error("Reading `%s' in EDIF mode failed.\n", filename);
	}
}
#endif

#ifdef VERIFIC_LIBERTY_SUPPORT
void VerificCommand::read_liberty()
{
	bool flag_lib = false;
	for (argidx++; argidx < GetSize(args); argidx++) {
		if (args[argidx] == "-lib") {
			flag_lib = true;
			continue;
		}
		if (args[argidx].compare(0, 1, "-") == 0) {
			pass.cmd_error(args, argidx, "unknown option");
			return;
		}
		break;
	}

	while (argidx < GetSize(args)) {
		std::string filename = frontend_rewrite();
		if (!synlib_file::Read(filename.c_str(), is_work_set ? work.c_str() : nullptr))
			log_cmd_error("Reading `%s' in LIBERTY mode failed.\n", filename);
		SynlibLibrary *lib = synlib_file::GetLastLibraryAnalyzed();
		if (lib && flag_lib) {
			MapIter mi ;
			Verific::Cell *c ;
			FOREACH_CELL_OF_LIBRARY(lib->GetLibrary(),mi,c) {
				MapIter ni ;
				Netlist *nl;
				FOREACH_NETLIST_OF_CELL(c, ni, nl) {
					if (nl)
						nl->MakeBlackBox();
				}
			}
		}
	}
}
#endif

void VerificCommand::pretty_print()
{
	const char* filename = nullptr;
	const char* module = nullptr;
	bool mode_vhdl = false;
	for (argidx++; argidx < GetSize(args); argidx++) {
#ifdef VERIFIC_VHDL_SUPPORT
		if (args[argidx] == "-vhdl") {
			mode_vhdl = true;
			continue;
		}
#endif
		if (args[argidx] == "-verilog") {
			mode_vhdl = false;
			continue;
		}

		if (args[argidx].compare(0, 1, "-") == 0) {
			pass.cmd_error(args, argidx, "unknown option");
			return;
		}

		if (!filename) {
			filename = args[argidx].c_str();
			continue;
		}
		if (module)
			log_cmd_error("Only one module can be specified.\n");
		module = args[argidx].c_str();
	}

	if (argidx < GetSize(args))
		pass.cmd_error(args, argidx, "unknown option/parameter");

	if (!filename)
		log_cmd_error("Filename must be specified.\n");

	if (mode_vhdl) {
#ifdef VERIFIC_VHDL_SUPPORT
		vhdl_file::PrettyPrint(filename, module, work.c_str());
#endif
		return;
	}
#ifdef VERIFIC_SYSTEMVERILOG_SUPPORT
	veri_file::PrettyPrint(filename, module, work.c_str());
#endif
}

void VerificCommand::import_design()
{
	std::map<std::string,Netlist*> nl_todo, nl_done;
	bool mode_all = false, mode_gates = false, mode_keep = false;
	bool mode_nosva = false, mode_sva_continue = false;
	bool mode_names = false, mode_verific = false;
	bool mode_autocover = false, mode_fullinit = false;
	bool flatten = false, extnets = false, mode_cells = false;
	bool split_complex_ports = true;
	string dumpfile;
	string ppfile;
	Map parameters(STRING_HASH);

	for (argidx++; argidx < GetSize(args); argidx++) {
		if (args[argidx] == "-all") {
			mode_all = true;
			continue;
		}
		if (args[argidx] == "-gates") {
			mode_gates = true;
			continue;
		}
		if (args[argidx] == "-flatten") {
			flatten = true;
			continue;
		}
		if (args[argidx] == "-no-split-complex-ports") {
			split_complex_ports = false;
			continue;
		}
		if (args[argidx] == "-extnets") {
			extnets = true;
			continue;
		}
		if (args[argidx] == "-k") {
			mode_keep = true;
			continue;
		}
#ifdef VERIFIC_SYSTEMVERILOG_SUPPORT
		if (args[argidx] == "-nosva") {
			mode_nosva = true;
			continue;
		}
		if (args[argidx] == "-sva-continue-on-err") {
			mode_sva_continue = true;
			continue;
		}
		if (args[argidx] == "-L" && argidx+1 < GetSize(args)) {
			verific_sva_fsm_limit = atoi(args[++argidx].c_str());
			continue;
		}
		if (args[argidx] == "-autocover") {
			mode_autocover = true;
			continue;
		}
#endif
		if (args[argidx] == "-n") {
			mode_names = true;
			continue;
		}
		if (args[argidx] == "-fullinit") {
			mode_fullinit = true;
			continue;
		}
		if (args[argidx] == "-cells") {
			mode_cells = true;
			continue;
		}
		if (args[argidx] == "-chparam"  && argidx+2 < GetSize(args)) {
			const std::string &key = args[++argidx];
			const std::string &value = args[++argidx];
			unsigned new_insertion = parameters.Insert(key.c_str(), value.c_str(),
									   1 /* force_overwrite */);
			if (!new_insertion)
				log_warning_noprefix("-chparam %s already specified: overwriting.\n", key);
			continue;
		}
		if (args[argidx] == "-V") {
			mode_verific = true;
			continue;
		}
		if (args[argidx] == "-v") {
			verific_verbose = 1;
			continue;
		}
		if (args[argidx] == "-vv") {
			verific_verbose = 2;
			continue;
		}
		if (args[argidx] == "-d" && argidx+1 < GetSize(args)) {
			dumpfile = args[++argidx];
			continue;
		}
		if (args[argidx] == "-pp" && argidx+1 < GetSize(args)) {
			ppfile = args[++argidx];
			continue;
		}
		break;
	}

	if (argidx > GetSize(args) && args[argidx].compare(0, 1, "-") == 0)
		pass.cmd_error(args, argidx, "unknown option");

	if ((unsigned long)verific_sva_fsm_limit >= sizeof(1ull)*8)
		log_cmd_error("-L %d: limit too large; maximum allowed value is %zu.\n", verific_sva_fsm_limit, sizeof(1ull)*8-1);

	if (already_imported)
		log_warning("Note that all Verific flags were reset to defaults after last -import.\n");

	std::set<std::string> top_mod_names;

	if (mode_all)
	{
		import_all(work.c_str(), &nl_todo, &parameters, true, ppfile);
	}
	else
	{
		if (argidx == GetSize(args))
			pass.cmd_error(args, argidx, "No top module specified.\n");

		std::vector<std::string> tops;
		for (int i = argidx; i < GetSize(args); i++)
			tops.push_back(args[i].c_str());
		top_mod_names = import_tops(work.c_str(), &nl_todo, &parameters, true, ppfile, tops) ;
	}
	if (mode_cells) {
		log("Importing all cells.\n");
		Libset *gls = Libset::Global() ;
		MapIter it ;
		Library *l ;
		FOREACH_LIBRARY_OF_LIBSET(gls,it,l) {
			MapIter mi ;
			Verific::Cell *c ;
			FOREACH_CELL_OF_LIBRARY(l,mi,c) {
				if (!mode_verific && (l == Library::Primitives() || l == Library::Operators())) continue;
				MapIter ni ;
				if (c->NumOfNetlists() == 1) {
					c->GetFirstNetlist()->SetName("");
				}
				Netlist *nl;
				FOREACH_NETLIST_OF_CELL(c, ni, nl) {
					if (nl)
						nl_todo.emplace(nl->CellBaseName(), nl);
				}
			}
		}
	}

	if (!verific_error_msg.empty())
		return;

	if (flatten) {
		for (auto nl : nl_todo)
			nl.second->Flatten();
	}

	if (extnets)
		verific_extnets(nl_todo);

	if (split_complex_ports) {
		for (auto nl : nl_todo)
			nl.second->ChangePortBusStructures(1 /* hierarchical */);
	}

#ifdef VERIFIC_SYSTEMVERILOG_SUPPORT
	if (!dumpfile.empty()) {
		VeriWrite veri_writer;
		veri_writer.WriteFile(dumpfile.c_str(), Netlist::PresentDesign());
	}
#endif
	while (!nl_todo.empty()) {
		auto it = nl_todo.begin();
		Netlist *nl = it->second;
		if (nl_done.count(it->first) == 0) {
			VerificImporter importer(mode_gates, mode_keep, mode_nosva, mode_sva_continue,
					mode_names, mode_verific, mode_autocover, mode_fullinit);
			nl_done[it->first] = it->second;
			importer.import_netlist(design, nl, nl_todo, top_mod_names.count(nl->CellBaseName()));
		}
		nl_todo.erase(it);
	}

	already_imported = true;
}

void VerificCommand::configure()
{
	if (argidx+1 == GetSize(args)) {
		MapIter mi;
		const char *k, *s;
		unsigned long v;
		pool<std::string> lines;
		FOREACH_MAP_ITEM(RuntimeFlags::GetVarMap(), mi, &k, &v) {
			lines.insert(stringf("%s %lu", k, v));
		}
		FOREACH_MAP_ITEM(RuntimeFlags::GetStringVarMap(), mi, &k, &s) {
			if (s == nullptr)
				lines.insert(stringf("%s NULL", k));
			else
				lines.insert(stringf("%s \"%s\"", k, s));
		}
		lines.sort();
		for (auto &line : lines)
			log("verific -cfg %s\n", line);
		return;
	}

	if (argidx+2 == GetSize(args)) {
		const char *k = args[argidx+1].c_str();
		if (RuntimeFlags::HasUnsignedVar(k)) {
			log("verific -cfg %s %lu\n", k, RuntimeFlags::GetVar(k));
			return;
		}
		if (RuntimeFlags::HasStringVar(k)) {
			const char *s = RuntimeFlags::GetStringVar(k);
			if (s == nullptr)
				log("verific -cfg %s NULL\n", k);
			else
				log("verific -cfg %s \"%s\"\n", k, s);
			return;
		}
		log_cmd_error("Can't find Verific Runtime flag '%s'.\n", k);
	}

	if (argidx+3 == GetSize(args)) {
		const auto &k = args[argidx+1], &v = args[argidx+2];
		if (v == "NULL") {
			RuntimeFlags::SetStringVar(k.c_str(), nullptr);
			return;
		}
		if (v[0] == '"') {
			std::string s = v.substr(1, GetSize(v)-2);
			RuntimeFlags::SetStringVar(k.c_str(), s.c_str());
			return;
		}
		char *endptr;
		unsigned long n = strtol(v.c_str(), &endptr, 0);
		if (*endptr == 0) {
			RuntimeFlags::SetVar(k.c_str(), n);
			return;
		}
	}

	run_extension();
}

void VerificCommand::run_extension()
{
#ifdef YOSYSHQ_VERIFIC_EXTENSIONS
	if (VerificExtensions::Execute(args, argidx, work,
		[this](const std::vector<std::string> &args, size_t argidx, std::string msg)
			{ pass.cmd_error(args, argidx, msg); } ))
		return;
#endif
	pass.cmd_error(args, argidx, "Missing or unsupported mode parameter.\n");
}

YOSYS_NAMESPACE_END
