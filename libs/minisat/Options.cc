#ifndef __STDC_FORMAT_MACROS
#define __STDC_FORMAT_MACROS
#endif
#ifndef __STDC_LIMIT_MACROS
#define __STDC_LIMIT_MACROS
#endif
/**************************************************************************************[Options.cc]
Copyright (c) 2008-2010, Niklas Sorensson

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#include "Sort.h"
#include "Options.h"
#include "ParseUtils.h"

using namespace Minisat;

void Minisat::parseOptions(int& argc, char** argv, bool strict)
{
    int i, j;
    for (i = j = 1; i < argc; i++){
        const char* str = argv[i];
        if (match(str, "--") && match(str, Option::getHelpPrefixString()) && match(str, "help")){
            if (*str == '\0')
                printUsageAndExit(argc, argv);
            else if (match(str, "-verb"))
                printUsageAndExit(argc, argv, true);
        } else {
            bool parsed_ok = false;
        
            for (int k = 0; !parsed_ok && k < Option::getOptionList().size(); k++){
                parsed_ok = Option::getOptionList()[k]->parse(argv[i]);

                // fprintf(stderr, "checking %d: %s against flag <%s> (%s)\n", i, argv[i], Option::getOptionList()[k]->name, parsed_ok ? "ok" : "skip");
            }

            if (!parsed_ok){
                if (strict && match(argv[i], "-"))
                    fprintf(stderr, "ERROR! Unknown flag \"%s\". Use '--%shelp' for help.\n", argv[i], Option::getHelpPrefixString()), exit(1);
                else
                    argv[j++] = argv[i];
            }
        }
    }

    argc -= (i - j);
}


void Minisat::setUsageHelp      (const char* str){ Option::getUsageString() = str; }
void Minisat::setHelpPrefixStr  (const char* str){ Option::getHelpPrefixString() = str; }
void Minisat::printUsageAndExit (int /*argc*/, char** argv, bool verbose)
{
    const char* usage = Option::getUsageString();
    if (usage != NULL)
        fprintf(stderr, usage, argv[0]);

    sort(Option::getOptionList(), Option::OptionLt());

    const char* prev_cat  = NULL;
    const char* prev_type = NULL;

    for (int i = 0; i < Option::getOptionList().size(); i++){
        const char* cat  = Option::getOptionList()[i]->category;
        const char* type = Option::getOptionList()[i]->type_name;

        if (cat != prev_cat)
            fprintf(stderr, "\n%s OPTIONS:\n\n", cat);
        else if (type != prev_type)
            fprintf(stderr, "\n");

        Option::getOptionList()[i]->help(verbose);

        prev_cat  = Option::getOptionList()[i]->category;
        prev_type = Option::getOptionList()[i]->type_name;
    }

    fprintf(stderr, "\nHELP OPTIONS:\n\n");
    fprintf(stderr, "  --%shelp        Print help message.\n", Option::getHelpPrefixString());
    fprintf(stderr, "  --%shelp-verb   Print verbose help message.\n", Option::getHelpPrefixString());
    fprintf(stderr, "\n");
    exit(0);
}

