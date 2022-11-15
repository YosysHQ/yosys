from pygments.lexer import RegexLexer, bygroups, include
from pygments.token import Comment, Keyword, Name, Number, String, Whitespace

__all__ = ['RtlilLexer']

class RtlilLexer(RegexLexer):
    name = 'RTLIL'
    aliases = ['rtlil']
    filenames = ['*.il']

    keyword_re = r'(always|assign|attribute|autoidx|case|cell|connect|edge|end|global|high|init|inout|input|low|memory|module|negedge|offset|output|parameter|posedge|process|real|signed|size|switch|sync|update|upto|width|wire)'
    
    tokens = {
        'common': [
            (r'\s+', Whitespace),
            (r'#.*', Comment.Single),
            (keyword_re, Keyword),
            (r'([\\\$][^ \t\r\n]+|\.[0-9]+)', Name.Variable),
            (r"[0-9]+'[01xzm-]*", Number),
            (r'-?[0-9]+', Number.Integer),
            (r'"', String, 'string'),
        ],
        'root': [
            (r'cell', Keyword, 'cell_definition'),
            (r'(module|wire|memory|process)', Keyword, 'definition'),
            include('common'),
        ],
        'definition': [
            (r'([\\\$][^ \t\r\n]+|\.[0-9]+)', Name.Entity, '#pop'),
            include('common')
        ],
        'cell_definition': [
            (r'(\$[^ \t\r\n]+)\b', Name.Function),
            (r'(\\[^ \t\r\n]+|\.[0-9]+)', Name.Variable),
            (r'$', Whitespace, '#pop'),
            include('common'),
        ],
        'string': [
            (r'"', String, '#pop'),
            (r'\\([\\abfnrtv"\']|x[a-fA-F0-9]{2,4}|[0-7]{1,3})', String.Escape),
            (r'[^\\"\n]+', String),  # all other characters
            (r'(\\)(\n)', bygroups(String.Escape, Whitespace)),  # line continuation
            (r'\\', String),  # stray backslash
        ]
    }
