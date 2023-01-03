/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2022  Jannis Harder <jix@yosyshq.com> <me@jix.one>
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

#ifndef JSON_H
#define JSON_H

#include "kernel/yosys.h"
#include "libs/json11/json11.hpp"
#include <functional>

YOSYS_NAMESPACE_BEGIN

using json11::Json;

class PrettyJson
{
    enum Scope {
        VALUE,
        OBJECT_FIRST,
        OBJECT,
        ARRAY_FIRST,
        ARRAY,
    };

    struct Target {
        virtual void emit(const char *data) = 0;
        virtual void flush() {};
        virtual ~Target() {};
    };

    std::string newline_indent = "\n";
    std::vector<std::unique_ptr<Target>> targets;
    std::vector<Scope> state = {VALUE};
    int compact_depth = INT_MAX;
public:

    void emit_to_log();
    void append_to_string(std::string &target);
    bool write_to_file(const std::string &path);

    bool active() { return !targets.empty(); }

    void compact() { compact_depth = GetSize(state); }

    void line(bool space_if_inline = true);
    void raw(const char *raw_json);
    void flush();
    void begin_object();
    void begin_array();
    void end_object();
    void end_array();
    void name(const char *name);
    void begin_value();
    void end_value();
    void value_json(const Json &value);
    void value(unsigned int value) { value_json(Json((int)value)); }
    template<typename T>
    void value(T &&value) { value_json(Json(std::forward<T>(value))); };

    void entry_json(const char *name, const Json &value);
    void entry(const char *name, unsigned int value) { entry_json(name, Json((int)value)); }
    template<typename T>
    void entry(const char *name, T &&value) { entry_json(name, Json(std::forward<T>(value))); };

    template<typename T>
    void object(const T &&values)
    {
        begin_object();
        for (auto &item : values)
            entry(item.first, item.second);
        end_object();
    }

    template<typename T>
    void array(const T &&values)
    {
        begin_object();
        for (auto &item : values)
            value(item);
        end_object();
    }
};



YOSYS_NAMESPACE_END

#endif
