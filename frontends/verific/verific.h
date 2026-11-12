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

#ifndef VERIFIC_H
#define VERIFIC_H

#ifdef YOSYS_ENABLE_VERIFIC

#include <condition_variable>
#include <mutex>

#include "DataBase.h"

#include "frontends/verific/verific_clocking.h"
#include "frontends/verific/verific_importer.h"

YOSYS_NAMESPACE_BEGIN

extern int verific_verbose;

bool check_noverific_env();
void verific_setup();

struct VerificSession {
	~VerificSession();
	static void begin(Design *design);
	static std::unique_ptr<VerificSession> deferred_end(Design *design);
private:
	static inline std::mutex mutex;
	static inline std::condition_variable cv;
	static inline Design *owner = nullptr;
};

extern bool verific_import_pending;
extern std::string verific_import(Design *design, const std::map<std::string,std::string> &parameters, std::string top = std::string());

extern pool<int> verific_sva_prims;

void verific_import_sva_assert(VerificImporter *importer, Verific::Instance *inst);
void verific_import_sva_assume(VerificImporter *importer, Verific::Instance *inst);
void verific_import_sva_cover(VerificImporter *importer, Verific::Instance *inst);
void verific_import_sva_trigger(VerificImporter *importer, Verific::Instance *inst);
bool verific_is_sva_net(VerificImporter *importer, Verific::Net *net);

extern int verific_sva_fsm_limit;

extern std::string verific_error_msg;

std::string get_full_netlist_name(Verific::Netlist *nl);
void save_blackbox_msg_state();
void restore_blackbox_msg_state();
void import_all(const char* work, std::map<std::string,Verific::Netlist*> *nl_todo, Verific::Map *parameters, bool show_message, std::string ppfile);
std::set<std::string> import_tops(const char* work, std::map<std::string,Verific::Netlist*> *nl_todo, Verific::Map *parameters, bool show_message, std::string ppfile, std::vector<std::string> &tops, std::string *top = nullptr);
void verific_extnets(const std::map<std::string,Verific::Netlist*> &nl_todo);

YOSYS_NAMESPACE_END

#endif
#endif
