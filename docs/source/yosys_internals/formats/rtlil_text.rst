.. _chapter:textrtlil:

RTLIL text representation
-------------------------

This appendix documents the text representation of RTLIL in extended Backus-Naur
form (EBNF).

The grammar is not meant to represent semantic limitations. That is, the grammar
is "permissive", and later stages of processing perform more rigorous checks.

The grammar is also not meant to represent the exact grammar used in the RTLIL
frontend, since that grammar is specific to processing by lex and yacc, is even
more permissive, and is somewhat less understandable than simple EBNF notation.

Finally, note that all statements (rules ending in ``-stmt``) terminate in an
end-of-line. Because of this, a statement cannot be broken into multiple lines.

Lexical elements
~~~~~~~~~~~~~~~~

Characters
^^^^^^^^^^

An RTLIL file is a stream of bytes. Strictly speaking, a "character" in an RTLIL
file is a single byte. The lexer treats multi-byte encoded characters as
consecutive single-byte characters. While other encodings *may* work, UTF-8 is
known to be safe to use. Byte order marks at the beginning of the file will
cause an error.

ASCII spaces (32) and tabs (9) separate lexer tokens.

A ``nonws`` character, used in identifiers, is any character whose encoding
consists solely of bytes above ASCII space (32).

An ``eol`` is one or more consecutive ASCII newlines (10) and carriage returns
(13).

Identifiers
^^^^^^^^^^^

There are two types of identifiers in RTLIL:

-  Publically visible identifiers
-  Auto-generated identifiers

.. code:: BNF

    <id>            ::= <public-id> | <autogen-id>
    <public-id>     ::= \ <nonws>+
    <autogen-id>    ::= $ <nonws>+

Values
^^^^^^

A *value* consists of a width in bits and a bit representation, most
significant bit first. Bits may be any of:

-  ``0``: A logic zero value
-  ``1``: A logic one value
-  ``x``: An unknown logic value (or don't care in case patterns)
-  ``z``: A high-impedance value (or don't care in case patterns)
-  ``m``: A marked bit (internal use only)
-  ``-``: A don't care value

An *integer* is simply a signed integer value in decimal format. **Warning:**
Integer constants are limited to 32 bits. That is, they may only be in the range
:math:`[-2147483648, 2147483648)`. Integers outside this range will result in an
error.

.. code:: BNF

    <value>         ::= <decimal-digit>+ ' <binary-digit>*
    <decimal-digit> ::= 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9
    <binary-digit>  ::= 0 | 1 | x | z | m | -
    <integer>       ::= -? <decimal-digit>+

Strings
^^^^^^^

A string is a series of characters delimited by double-quote characters. Within
a string, any character except ASCII NUL (0) may be used. In addition, certain
escapes can be used:

-  ``\n``: A newline
-  ``\t``: A tab
-  ``\ooo``: A character specified as a one, two, or three digit octal value

All other characters may be escaped by a backslash, and become the following
character. Thus:

-  ``\\``: A backslash
-  ``\"``: A double-quote
-  ``\r``: An 'r' character

Comments
^^^^^^^^

A comment starts with a ``#`` character and proceeds to the end of the line. All
comments are ignored.

File
~~~~

A file consists of an optional autoindex statement followed by zero or more
modules.

.. code:: BNF

    <file> ::= <autoidx-stmt>? <module>*

Autoindex statements
^^^^^^^^^^^^^^^^^^^^

The autoindex statement sets the global autoindex value used by Yosys when it
needs to generate a unique name, e.g. ``flattenN``. The N part is filled with
the value of the global autoindex value, which is subsequently incremented. This
global has to be dumped into RTLIL, otherwise e.g. dumping and running a pass
would have different properties than just running a pass on a warm design.

.. code:: BNF

    <autoidx-stmt> ::= autoidx <integer> <eol>

Modules
^^^^^^^

Declares a module, with zero or more attributes, consisting of zero or more
wires, memories, cells, processes, and connections.

.. code:: BNF

    <module>            ::= <attr-stmt>* <module-stmt> <module-body> <module-end-stmt>
    <module-stmt>       ::= module <id> <eol>
    <module-body>       ::= (<param-stmt> 
                         |   <wire> 
                         |   <memory> 
                         |   <cell> 
                         |   <process>)*
    <param-stmt>        ::= parameter <id> <constant>? <eol>
    <constant>          ::= <value> | <integer> | <string>
    <module-end-stmt>   ::= end <eol>

Attribute statements
^^^^^^^^^^^^^^^^^^^^

Declares an attribute with the given identifier and value.

.. code:: BNF

    <attr-stmt> ::= attribute <id> <constant> <eol>

Signal specifications
^^^^^^^^^^^^^^^^^^^^^

A signal is anything that can be applied to a cell port, i.e. a constant value,
all bits or a selection of bits from a wire, or concatenations of those.

**Warning:** When an integer constant is a sigspec, it is always 32 bits wide,
2's complement. For example, a constant of :math:`-1` is the same as
``32'11111111111111111111111111111111``, while a constant of :math:`1` is the
same as ``32'1``.

See :ref:`sec:rtlil_sigspec` for an overview of signal specifications.

.. code:: BNF

    <sigspec> ::= <constant> 
               |  <wire-id>
               |  <sigspec> [ <integer> (:<integer>)? ] 
               |  { <sigspec>* }

Connections
^^^^^^^^^^^

Declares a connection between the given signals.

.. code:: BNF

    <conn-stmt> ::= connect <sigspec> <sigspec> <eol>

Wires
^^^^^

Declares a wire, with zero or more attributes, with the given identifier and
options in the enclosing module.

See :ref:`sec:rtlil_cell_wire` for an overview of wires.

.. code:: BNF

    <wire>          ::= <attr-stmt>* <wire-stmt>
    <wire-stmt>     ::= wire <wire-option>* <wire-id> <eol>
    <wire-id>       ::= <id>
    <wire-option>   ::= width <integer> 
                     |  offset <integer> 
                     |  input <integer> 
                     |  output <integer> 
                     |  inout <integer> 
                     |  upto 
                     |  signed

Memories
^^^^^^^^

Declares a memory, with zero or more attributes, with the given identifier and
options in the enclosing module.

See :ref:`sec:rtlil_memory` for an overview of memory cells, and
:ref:`sec:memcells` for details about memory cell types.

.. code:: BNF

    <memory>        ::= <attr-stmt>* <memory-stmt>
    <memory-stmt>   ::= memory <memory-option>* <id> <eol>
    <memory-option> ::= width <integer> 
                     |  size <integer> 
                     |  offset <integer>

Cells
^^^^^

Declares a cell, with zero or more attributes, with the given identifier and
type in the enclosing module.

Cells perform functions on input signals. See
:doc:`/yosys_internals/formats/cell_library` for a detailed list of cell types.

.. code:: BNF

    <cell>              ::= <attr-stmt>* <cell-stmt> <cell-body-stmt>* <cell-end-stmt>
    <cell-stmt>         ::= cell <cell-type> <cell-id> <eol>
    <cell-id>           ::= <id>
    <cell-type>         ::= <id>
    <cell-body-stmt>    ::= parameter (signed | real)? <id> <constant> <eol>
                         |  connect <id> <sigspec> <eol>
    <cell-end-stmt>     ::= end <eol>


Processes
^^^^^^^^^

Declares a process, with zero or more attributes, with the given identifier in
the enclosing module. The body of a process consists of zero or more
assignments, exactly one switch, and zero or more syncs.

See :ref:`sec:rtlil_process` for an overview of processes.

.. code:: BNF

    <process>       ::= <attr-stmt>* <proc-stmt> <process-body> <proc-end-stmt>
    <proc-stmt>     ::= process <id> <eol>
    <process-body>  ::= <assign-stmt>* <switch>? <assign-stmt>* <sync>*
    <assign-stmt>   ::= assign <dest-sigspec> <src-sigspec> <eol>
    <dest-sigspec>  ::= <sigspec>
    <src-sigspec>   ::= <sigspec>
    <proc-end-stmt> ::= end <eol>

Switches
^^^^^^^^

Switches test a signal for equality against a list of cases. Each case specifies
a comma-separated list of signals to check against. If there are no signals in
the list, then the case is the default case. The body of a case consists of zero
or more switches and assignments. Both switches and cases may have zero or more
attributes.

.. code:: BNF

    <switch>            ::= <switch-stmt> <case>* <switch-end-stmt>
    <switch-stmt>        := <attr-stmt>* switch <sigspec> <eol>
    <case>              ::= <attr-stmt>* <case-stmt> <case-body>
    <case-stmt>         ::= case <compare>? <eol>
    <compare>           ::= <sigspec> (, <sigspec>)*
    <case-body>         ::= (<switch> | <assign-stmt>)*
    <switch-end-stmt>   ::= end <eol>

Syncs
^^^^^

Syncs update signals with other signals when an event happens. Such an event may
be:

-  An edge or level on a signal
-  Global clock ticks
-  Initialization
-  Always

.. code:: BNF

    <sync>          ::= <sync-stmt> <update-stmt>*
    <sync-stmt>     ::= sync <sync-type> <sigspec> <eol> 
                     |  sync global <eol>
                     |  sync init <eol> 
                     |  sync always <eol>
    <sync-type>     ::= low | high | posedge | negedge | edge
    <update-stmt>   ::= update <dest-sigspec> <src-sigspec> <eol>
