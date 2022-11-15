from pygments.lexer import RegexLexer, bygroups, include
from pygments.token import (Comment, Error, Keyword, Name, Number, Operator,
                            String, Whitespace)

__all__ = ['YoscryptLexer']

class YoscryptLexer(RegexLexer):
    name = 'Yosys Script'
    aliases = ['yoscrypt']
    filenames = ['*.ys']
    
    
    
    tokens = {
        'common': [
            (r'\s+', Whitespace),
            (r'#.*', Comment.Single),
            (r'"', String, 'string'),
            (r'(\d+)(\')([bdho]? ?\w+)', bygroups(Number, Operator, Number)),
            (r'(\d+\.\d+)', Number.Float),
            (r'(\d+)', Number),
            (r'(\$[A-Za-z_0-9]*)', Name.Builtin),
            (r'([A-Za-z_][A-Za-z_0-9\.\\/:-]*)', Name),
            (r'(\[)(-\S*)(\])', # optional command
             	bygroups(Operator, Name.Attribute, Operator)),
            (r'([\[<]\w*[\]>])', Name), # arguments
            (r'[\{\}\|=\[\],]', Operator),
            (r'.', Comment),
        ],
        'root': [
            (r'([A-Za-z_][A-Za-z_0-9]*)', Keyword, 'command'),
            (r'(-[A-Za-z_][A-Za-z_0-9]*)', Name.Attribute, 'command'), # shortcut for options
            include('common'),
        ],
        'command': [
            (r'(-[A-Za-z_][A-Za-z_0-9]*)', Name.Attribute),
            (r'\+/[^\s]+', Name.Class),
            (r'$', Whitespace, '#pop'),
            (r';(?=\s)', Operator, '#pop'),
            (r';{2,3}(?=\s)', Name.Class, '#pop'),
            (r';{1,3}', Error, '#pop'),
            (r'([ANwismctparn]:)', Keyword.Type, 'pattern'),
            (r'@', Keyword.Type),
            (r'%(x|ci|co)e?', Keyword.Type, 'expansion'),
            (r'%[%nuidDcasmMCR]?', Keyword.Type),
            (r'/', Operator),
            include('common'),
        ],
        'pattern': [
            (r'<<', Name), # Not an operator
            (r'(=|<|<=|>|>=)', Operator),
            (r':', Keyword.Type),
            (r'$', Whitespace, '#pop:2'),
            (r'\s+', Whitespace, '#pop'),
            include('common'),
        ],
        'expansion': [
            (r'$', Name.Class, '#pop:2'),
            (r';(?=\s)', Operator, '#pop:2'),
            (r';{2,3}(?=\s)', Name.Class, '#pop:2'),
            (r'\s', Whitespace, '#pop'),
            (r'[0-9\*]{1,3}', Number),
            (r'[:+-,\[\]]', Operator),
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
