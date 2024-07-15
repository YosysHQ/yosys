/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2024  Emily Schmidt <emily@yosyshq.com>
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

#include "sexpr.h"

YOSYS_NAMESPACE_BEGIN

std::ostream &operator<<(std::ostream &os, SExpr const &sexpr) {
    if(sexpr.is_atom())
        os << sexpr.atom();
    else if(sexpr.is_list()){
        os << "(";
        auto l = sexpr.list();
        for(size_t i = 0; i < l.size(); i++) {
            if(i > 0) os << " ";
            os << l[i];
        }
        os << ")";
    }else
        os << "<invalid>";
    return os;
}

 std::string SExpr::to_string() const {
    std::stringstream ss;
    ss << *this;
    return ss.str();
}

void SExprWriter::nl_if_pending() {
    if(_pending_nl) {
        os << '\n';
        _pos = 0;
        _pending_nl = false;
    }
}

void SExprWriter::puts(std::string_view s) {
    if(s.empty()) return;
    nl_if_pending();
    for(auto c : s) {
        if(c == '\n') {
            os << c;
            _pos = 0;
        } else {
            if(_pos == 0) {
                for(int i = 0; i < _indent; i++)
                    os << "  ";
                _pos = 2 * _indent;
            }
            os << c;
            _pos++;
        }
    }
}


// Calculate how much space would be left if expression was written
// out in full horizontally. Returns any negative value if it doesn't fit.
//
// (Ideally we would avoid recalculating the widths of subexpression,
// but I can't figure out how to store the widths. As an alternative,
// we bail out of the calculation as soon as we can tell the expression
// doesn't fit in the available space.)
int SExprWriter::check_fit(SExpr const &sexpr, int space) {
    if(sexpr.is_atom())
        return space - sexpr.atom().size();
    else if(sexpr.is_list()) {
        space -= 2;
        if(sexpr.list().size() > 1)
            space -= sexpr.list().size() - 1;
        for(auto arg : sexpr.list()) {
            if(space < 0) break;
            space = check_fit(arg, space);
        }
        return space;
    } else
        return -1;
}

void SExprWriter::print(SExpr const &sexpr, bool close, bool indent_rest) {
    if(sexpr.is_atom())
        puts(sexpr.atom());
    else if(sexpr.is_list()) {
        auto args = sexpr.list();
        puts("(");
        // Expressions are printed horizontally if they fit on the line.
        // We do the check *after* puts("(") to make sure that _pos is accurate.
        // (Otherwise there could be a pending newline + indentation)
        bool vertical = args.size() > 1 && check_fit(sexpr, _max_line_width - _pos + 1) < 0;
        if(vertical) _indent++;
        for(size_t i = 0; i < args.size(); i++) {
            if(i > 0) puts(vertical ? "\n" : " ");
            print(args[i]);
        }
        // Any remaining arguments are currently always printed vertically,
        // but are not indented if indent_rest = false.
        _indent += (!close && indent_rest) - vertical;
        if(close)
            puts(")");
        else {
            _unclosed.push_back(indent_rest);
            _pending_nl = true;
        }
    }else
        log_error("shouldn't happen: SExpr '%s' is neither an atom nor a list", sexpr.to_string().c_str());
}

void SExprWriter::close(size_t n) {
    log_assert(_unclosed.size() - (_unclosed_stack.empty() ? 0 : _unclosed_stack.back()) >= n);
    while(n-- > 0) {
        bool indented = _unclosed[_unclosed.size() - 1];
        _unclosed.pop_back();
        // Only print ) on the same line if it fits.
        _pending_nl = _pos >= _max_line_width;
        if(indented)
            _indent--;
        puts(")");
        _pending_nl = true;
    }
}

void SExprWriter::comment(std::string const &str, bool hanging) {
    if(hanging) {
        if(_pending_nl) {
            _pending_nl = false;
            puts(" ");
        }
    }
    size_t i = 0, e;
    do{
        e = str.find('\n', i);
        puts("; ");
        puts(std::string_view(str).substr(i, e - i));
        puts("\n");
        i = e + 1;
    }while(e != std::string::npos);
}

SExprWriter::~SExprWriter() {
    while(!_unclosed_stack.empty())
        pop();
    close(_unclosed.size());
    nl_if_pending();
}

YOSYS_NAMESPACE_END
