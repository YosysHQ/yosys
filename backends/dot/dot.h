#ifndef DOT_BACKEND_H
#define DOT_BACKEND_H

#include "kernel/yosys.h"
#include "kernel/register.h"
#include "kernel/celltypes.h"
#include "kernel/log.h"
#include "kernel/sigtools.h"
#include <stdio.h>

YOSYS_NAMESPACE_BEGIN

namespace DOT_BACKEND {
    class ShowWorker {
    private:

        CellTypes ct;

        vector<shared_str> dot_escape_store;
        std::map<RTLIL::IdString, int> dot_id2num_store;
        std::map<RTLIL::IdString, int> autonames;
        int single_idx_count;

        struct net_conn {
            std::set<std::string> in, out; int bits; std::string color;
        };
        std::map<std::string, net_conn> net_conn_map;

        FILE *f;
        RTLIL::Design *design;
        RTLIL::Module *module;
        uint32_t currentColor;
        bool genWidthLabels;
        bool genSignedLabels;
        bool stretchIO;
        bool enumerateIds;
        bool abbreviateIds;
        bool notitle;
        int page_counter;

        const std::vector<std::pair<std::string, RTLIL::Selection>> &color_selections;
        const std::vector<std::pair<std::string, RTLIL::Selection>> &label_selections;

        std::map<RTLIL::Const, int> colorattr_cache;
        RTLIL::IdString colorattr;


        static uint32_t xorshift32(uint32_t x);

        std::string nextColor();


        std::string nextColor(std::string presetColor);


        std::string nextColor(RTLIL::SigSpec sig, std::string defaultColor);


        std::string nextColor(const RTLIL::SigSig &conn, std::string defaultColor);


        std::string nextColor(const RTLIL::SigSpec &sig);


        std::string nextColor(const RTLIL::SigSig &conn);


        std::string widthLabel(int bits);


        const char *findColor(std::string member_name);


        const char *findLabel(std::string member_name);


        const char *escape(std::string id, bool is_name = false);


        int id2num(RTLIL::IdString id);


        std::string gen_signode_simple(RTLIL::SigSpec sig, bool range_check = true);


        std::string gen_portbox(std::string port, RTLIL::SigSpec sig, bool driver, std::string *node = NULL);


        void collect_proc_signals(std::vector<RTLIL::SigSpec> &obj, std::set<RTLIL::SigSpec> &signals);


        void collect_proc_signals(std::vector<RTLIL::SigSig> &obj, std::set<RTLIL::SigSpec> &input_signals, std::set<RTLIL::SigSpec> &output_signals);


        void collect_proc_signals(RTLIL::CaseRule *obj, std::set<RTLIL::SigSpec> &input_signals, std::set<RTLIL::SigSpec> &output_signals);


        void collect_proc_signals(RTLIL::SwitchRule *obj, std::set<RTLIL::SigSpec> &input_signals, std::set<RTLIL::SigSpec> &output_signals);


        void collect_proc_signals(RTLIL::SyncRule *obj, std::set<RTLIL::SigSpec> &input_signals, std::set<RTLIL::SigSpec> &output_signals);


        void collect_proc_signals(RTLIL::Process *obj, std::set<RTLIL::SigSpec> &input_signals, std::set<RTLIL::SigSpec> &output_signals);


    public:
        void handle_module();


        /* TODO: enable usage of iostreams */
        // ShowWorker(std::ostream *s, RTLIL::Design *design,) : f(NULL), s {}


        ShowWorker(FILE *, RTLIL::Design *, std::vector<RTLIL::Design*> &, uint32_t , bool ,
                   bool , bool , bool , bool , bool ,
                   const std::vector<std::pair<std::string, RTLIL::Selection>> &,
                   const std::vector<std::pair<std::string, RTLIL::Selection>> &, RTLIL::IdString );
    };
}

YOSYS_NAMESPACE_END

#endif /* DOT_BACKEND_H */
