Generated help messages and documentation
=========================================

All Yosys commands and built-in cell types should include help text, documenting
their functionality for users.  This help text is made available through the
`help` command, and online via `ReadtheDocs`_ as part of the :doc:`/cmd_ref` and
:doc:`/cell_index` documentation.  When running locally, any commands provided
by loaded plugins (either from the command line when calling ``yosys``, or
dynamically with the `plugin` command) will also be available to the `help`
command.

.. _ReadtheDocs: https://about.readthedocs.com/

.. note::

   Since help text for commands is generated from compiled code, the online help
   may differ from that produced by `help`.  Some commands, like `abc`, may be
   completely unavailable depending on compile flags; while others may limit
   specific features, such as whether the `synth` script pass uses ABC.

Command help
------------

The first stop for command help text is the ``Pass::short_help``.  This is a
short sentence describing the pass, and is set in the ``Pass`` constructor with
the name of the pass, as demonstrated here with `chformal`.

.. literalinclude:: /generated/chformal.cc
   :language: c++
   :start-at: public Pass {
   :end-at: ChformalPass()
   :caption: ``ChformalPass()`` from :file:`passes/cmds/chformal.cc`
   :append: 
              // ...
      } ChformalPass;

All currently available commands are listed with their ``short_help`` string
when calling `help` without arguments, and is more or less the same as the
unlisted :ref:`command index <commandindex>`.  The string is also used when
hovering over links to commands in the documentation, and in section headings
like :ref:`chformal autocmd`.

The next section shows the complete help text for the `chformal` command.  This
can be displayed locally by using ``help <command>`` (or ``yosys -h <command>``
from the command line).  The general format is to show each usage signature (how
the command is called), followed by a paragraph describing what the pass does,
and a list of options or flags available.  Additional arguments in the signature
or option may use square brackets (``[]``) to indicate optional parts, and angle
brackets (``<>``) for required parts.  The pipe character ``|`` may be used to
indicate mutually exclusive arguments.

.. note::

   Remember that when using ``Frontend`` and ``Backend`` the pass name will be
   be prefixed with ``read_`` or ``write_`` respectively.  Usage signatures must
   match the pass name available in commands/scripts, which is available as
   ``Pass::pass_name``.

.. todo:: decide on a formatting style for pass options

.. _chformal autocmd:

.. autocmd:: chformal
   :noindex:

The ``Pass::help()`` method
~~~~~~~~~~~~~~~~~~~~~~~~~~~

Overriding this method is the original way to provide help text, and as of this
writing is still the most common.  The ``log()`` function should be called
directly to print and format the help text, and each line should be limited to
80 (printed) characters.  While it is possible to provide arbitrary formatting,
it is preferred to follow the guidelines here to maintain consistency with other
passes and to assist in correct parsing and formatting during RST generation
(i.e. these docs).

The first and last lines should always be blank (usually ``log("\n");``),
followed by the primary usage signature for the command.  Each usage signature
should be indented with 4 spaces, and followed by a blank line.  Each option or
flag should start on a new line indented with 4 spaces, followed by a
description of the option which is indented by a further 4 spaces, and then a
blank line. Option descriptions typically start with lower case, and may forgo a
trailing period (``.``). Where multiple options share a description the blank
line between options should be omitted.

.. note::

   `Dumping to json`_ has more on how formatting in ``help()`` gets parsed.


The ``Pass::formatted_help()`` method
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The ``formatted_help`` method serves two purposes in help generation, both of
which are optional.  In both cases, any pass which uses the method should
``#include "kernel/log_help.h"``, and begin the method by calling ``auto *help =
PrettyHelp::get_current();``.  The method finishes by returning a boolean value.
``true`` means help content has been added to the current ``PrettyHelp``, while
``false`` indicates that ``Pass::help()`` should be called instead.

Setting a command group
^^^^^^^^^^^^^^^^^^^^^^^

Command groups are used when `Dumping to json`_, so that related
commands can be presented together in documentation.  For example, all of the
formal commands (which `chformal` is one of) are listed under
:doc:`/cmd/index_formal`, by using the ``autocmdgroup`` directive in
:file:`docs/source/cmd/index_formal.rst`.  By default, commands are grouped by
their source location, such that the group is the same as the path to the source
file.  

.. note::

   Source location tracking requires :makevar:`ENABLE_HELP_SOURCE` to be set in
   the makefile.  Some passes, like the ``opt_*`` family, are able to be grouped
   by the name of the pass; but most will be assigned the ``unknown`` group.

   For frontends and backends, source code is structured such that different
   formats are located in different folders.  Default behavior is to instead
   group all of these passes as :doc:`/cmd/index_frontends` and
   :doc:`/cmd/index_backends` respectively.  Without location tracking, the
   fallback is to look for passes that start with ``read_`` or ``write_``.

It is possible to set the group of a command explicitly with the
``PrettyHelp::set_group()`` method.  This allows grouping of commands which may
not share a common source location, as well as ensuring that commands are still
grouped when location tracking is disabled.  Because ``Pass::formatted_help()``
returns if it produced help content, it is completely valid to override the
method, get the current instance of ``PrettyHelp``, set the command group, and
then return ``false``.

.. warning::

   There is currently no warning available for groups that do not have a
   corresponding ``autocmdgroup``.  If you add a new command group, make sure
   that it has a corresponding index page.


Rich help text
^^^^^^^^^^^^^^

The second purpose of ``Pass::formatted_help`` is to provide richer help
content which is able to take advantage of the reStructuredText formatting used
here in the web docs.  It also provides a more fluid way of writing help text,
without getting caught up in the terminal-first spacing requirements of writing
for ``Pass::help()``.

Help content is a list of ``ContentListing`` nodes on a root node, which can be
found by calling ``PrettyHelp::get_root()``.  Each node has a type, a body, and
its own list of children ``ContentListing``\ s.  Adding content is done with the
``ContentListing::{usage, option, codeblock, paragraph}`` methods, which each
add a new child node with a type set to the calling method.  Let's take a look
at the source code for `chformal`.

.. literalinclude:: /generated/chformal.cc
   :language: c++
   :start-at: bool formatted_help()
   :end-before: void execute
   :caption: ``ChformalPass::formatted_help()`` from :file:`passes/cmds/chformal.cc`

We can see that each of the ``ContentListing`` methods have the body of the new
node as the first argument.  For a ``usage`` node, this is how to call the
command (i.e. its usage signature).  ``paragraph`` nodes contain a paragraph of
text with line breaks added automatically; the argument itself should contain
any line breaks, but the string can be broken across multiple lines as shown.
The body of a ``paragraph`` node is treated as raw RST, allowing for inline
formatting and references as if it were written in the RST file itself.  As
shown in the example (and the :ref:`formatted output above <chformal autocmd>`),
this includes using single backticks for linking to cells or commands, and
double backticks for raw code.

The ``option`` method lists a single option for the command, usually starting
with a dash (``-``).  An optional second argument can be provided with adds a
paragraph node as a child of the option, and is used for describing the option.
Where multiple options share a description, it should be added to the last
option.  

.. note::

   To add multiple paragraphs to an option's description,
   ``ContentListing::open_option()`` should be used instead.  This method
   returns the option node, which can then be used to call
   ``ContentList::paragraph()`` multiple times.

``codeblock`` content is displayed verbatim, and content should include line
breaks as desired.  No extra formatting will be applied to the text, and it will
be rendered with a monospace font; making it perfect for code sections or ASCII
art diagrams which render the same on the web as they do in the terminal.  An
optional second argument is available for specifying the language in RST output
for code syntax highlighting (use ``yoscrypt`` for yosys script syntax
highlighting).

..
   not recommended since it (currently) doesn't render in the terminal

   The final method available is ``ContentListing::open_usage``.  As with
   ``open_option`` creates and returns a new node which can have additional content
   added to it directly.  For the usage node, this can be used for example to add
   text/options specific to a given usage of the command.  In the web documentation
   any content added in this way will be indented under the usage signature.


Command line rendering
~~~~~~~~~~~~~~~~~~~~~~

Rendering text for the command line is done by the ``Pass::help`` method.  When
this method is not overridden, the default behavior is to call
``Pass::formatted_help()``.  If this method is also left unimplemented, or the
return value is explicitly false, then a default message about missing help text
for the command is displayed.  Returning true, however, will then call
``PrettyHelp::log_help()`` to convert the formatted help content into plain
text.

Rendering rich help text as plain text is done by traversing over all the
``ContentListing`` nodes and printing the body text.  ``usage`` nodes are
preceded by an empty line and indented one level (4 spaces).  ``option`` nodes
are also indented one level, while their children are indented an extra level (8
spaces).  Each section of body text is broken into words separated by spaces.
If a word would cause the line to exceed 80 characters (controlled by
``MAX_LINE_LEN`` in :file:`kernel/log_help.cc`), then the word will instead be
placed on a new line, with the same level of indentation.

Special handling is included for words that begin and end with a backtick
(`````) so that these are stripped when printing to the command line.  Compare
:ref:`chformal_help` below with the :ref:`chformal autocmd` above.  The content
is still the same, but for the command line it uses a fixed width.

.. todo:: spaces in backticks (``assert(...)`` vs ````assert(s_eventually ...)````)

.. literalinclude:: /generated/chformal.log
   :lines: 2-
   :name: chformal_help
   :caption: Command line output for `help chformal`


Cell help
---------

- :file:`techlibs/common/simcells.v` and :file:`techlibs/common/simlib.v`
- parsed by :file:`techlibs/common/cellhelp.py`

  + unlike commands, cell help text is generated at compile time
  + only formatting occurs at run time
  + no support for custom cells in plugins

- comments preceding cell type converted to a ``SimHelper`` struct, defined in
  :file:`kernel/register.cc`
- ``#include``\ d in :file:`kernel/register.cc`, creating a map of cell types to
  their ``SimHelper`` struct.

- ``help -cells``

  - lists all cells with their input/output ports
  - again an unlisted :ref:`cell index <cellindex>`

- ``help <celltype>``

  - prints help message for ``<celltype>``
  - constructed from ``SimHelper`` content depending on version

- ``help <celltype>+``

  - prints verilog code for ``<celltype>``

v1 (default)
~~~~~~~~~~~~

- Legacy format
- Expects formatting as follows:

.. code-block:: verilog

   //-
   //-    $<celltype> (<ports>)
   //* group <cellgroup>
   //-
   //- <cell description>
   //-
   module \$<celltype> (<ports>);
   // ...
   endmodule

- ``//* group`` line is generally after the cell signature, but can appear
  anywhere in the comment block

  - determines where the cell is included in sphinx
  - check :file:`docs/source/cell` for current groups
  - a missing group will raise an error
  - assigning an unused group will result in the cell not being included in the
    sphinx docs

- the port signature line (``//-    $<celltype> (<ports>)``) must start with (at
  least) 4 spaces (not tabs)

  - the empty lines (``//-``) before/after the signature are required

- cell description can be multiple lines, but each line must start with ``//-``
  and a space

  - description should have a trailing empty line
  - line breaks are preserved in `help` calls but will be rendered as text in
    sphinx docs, with empty lines being required between paragraphs

- cells in :file:`techlibs/common/simcells.v` can have optional truth table at
  the end of the cell description which is rendered in sphinx docs as a literal
  code block
- e.g. `$_NOT_`:

.. code-block:: verilog

   //-
   //-     $_NOT_ (A, Y)
   //* group comb_simple
   //-
   //- An inverter gate.
   //-
   //- Truth table:    A | Y
   //-                ---+---
   //-                 0 | 1
   //-                 1 | 0
   //-

v2 (more expressive)
~~~~~~~~~~~~~~~~~~~~

- each field of the ``SimHelper`` struct can be assigned with:

.. code-block:: verilog

   //* <name> <value>

- ``ver`` must be explicitly set as ``2``
- optional fields ``title`` and ``tags``

  - title used for better displaying of cell
  - tags is a space-separated list of :doc:`/cell/properties`

- the port signature is automatically generated from the ``module`` definition
- cell description is the same as v1
- can link to commands or passes using backticks (`````)
- e.g. `$nex`:

.. code-block:: verilog

   //* ver 2
   //* title Case inequality
   //* group binary
   //* tags x-aware
   //- This corresponds to the Verilog '!==' operator.
   //-
   //- Refer to `$eqx` for more details.
   //-

- code blocks can be included as following:

.. code-block:: verilog

   //- text
   //- ::
   //-
   //-    monospaced text
   //-
   //-        indentation and line length will be preserved, giving a scroll bar if necessary for the browser window
   //-
   //- more text

- the empty line after the ``::`` and before the text continues are required
- the ``::`` line will be ignored in the `help` call while sphinx docs will
  treat everything that follows as a literal block until the next unindented
  line:

   text
   ::

      monospaced text

         indentation and line length will be preserved, giving a scroll bar if necessary for the browser window

   more text


Dumping to json
---------------

- `help -dump-cmds-json cmds.json`

  + generates a ``ContentListing`` for each command registered in Yosys
  + tries to parse unformatted ``Pass::help()`` output if
    ``Pass::formatted_help()`` is unimplemented or returns false

    * if a line starts with four spaces followed by the name of the command then
      a space, it is parsed as a signature (usage node)
    * if a line is indented and starts with a dash (``-``), it is parsed as an
      option
    * anything else is parsed as a codeblock and added to either the root node
      or the current option depending on the indentation

  + dictionary of command name to ``ContentListing``

    * uses ``ContentListing::to_json()`` recursively for each node in root
    * root node used for source location of class definition
    * includes flags set during pass constructor (e.g. ``experimental_flag`` set
      by ``Pass::experimental()``)
    * also title (``short_help`` argument in ``Pass::Pass``), group, and class
      name
   
  + dictionary of group name to list of commands in that group

- used by sphinx autodoc to generate help content

.. literalinclude:: /generated/cmds.json
   :language: json
   :start-at: "chformal": {
   :end-before: "chparam": {
   :caption: `chformal` in generated :file:`cmds.json`

.. note:: Synthesis command scripts are special cased

   If the final block of help output starts with the string ``"The following
   commands are executed by this synthesis command:\n"``, then the rest of the
   code block is formatted as ``yoscrypt`` (e.g. `synth_ice40`).  The caveat
   here is that if the ``script()`` calls ``run()`` on any commands *prior* to
   the first ``check_label`` then the auto detection will break and revert to
   unformatted code (e.g. `synth_fabulous`).


Cells and commands in Sphinx
----------------------------

To support the rich documentation of commands and cells in Yosys, we use two
custom `Sphinx Domains`_.  

.. _Sphinx Domains: https://www.sphinx-doc.org/en/master/usage/domains/index.html

- ``yoscrypt`` role allows inline code to have yosys script syntax highlighting
- default role of ``autoref``

  + any text in single backticks without an explicit role will be assigned this one
  + will convert to ``cell:ref`` if it begins with ``$``, otherwise ``cmd:ref``
  + to attempt linking there must be no spaces, and it must not begin with a
    dash (``-``)
  + ```chformal``` (or ``:autoref:`chformal```) -> ``:cmd:ref:`chformal``` -> `chformal`
  + also works with two words, if the first one is ``help``
  + ```help $add``` -> ``:cell:ref:`help $add <$add>``` -> `help $add`
  + fallback to formatting as inline yoscrypt
  + ```-remove``` -> `-remove`
  + ```chformal -remove``` -> ``:yoscrypt:`chformal -remove``` -> `chformal -remove`

Using autodoc
~~~~~~~~~~~~~

- below is the raw RST output from ``autocmd`` (``YosysCmdDocumenter`` class in
  :file:`docs/util/cmd_documenter.py`) for `chformal` command
- heading will be rendered as a subheading of the most recent heading (see
  `chformal autocmd`_ above rendered under `Command help`_)
- ``.. cmd:def:: <cmd>`` line is indexed for cross references with ``:cmd:ref:``
  directive (`chformal autocmd`_ above uses ``:noindex:`` option so that
  `chformal` still links to the correct location)

  + ``:title:`` option controls text that appears when hovering over the
    `chformal` link

- commands with warning flags (experimental or internal) add a ``.. warning``
  block before any of the help content
- if a command has no ``source_location`` the ``.. note`` at the bottom will
  instead link to :doc:`/cmd/index_other`

.. _showing autocmd generated rst:

.. autocmd_rst:: chformal

- command groups documented with ``autocmdgroup <group>``

  + with ``:members:`` option this is the same as calling ``autocmd`` for each
    member of the group

- ``autocell`` and ``autocellgroup``

  + very similar to ``autocmd`` and ``autocmdgroup`` but for cells instead of
    commands (``YosysCellDocumenter`` in :file:`docs/util/cell_documenter.py`)
  + optionally includes verilog source for cell(s) with ``:source:`` option
    (plus ``:linenos:``)
  + cell definitions do not include titles
  + cells can have properties (:ref:`propindex`)

- bonus ``autocmd_rst``, used exclusively on this page for `showing autocmd
  generated rst`_

Our custom Sphinx domains
~~~~~~~~~~~~~~~~~~~~~~~~~

- ``cmd`` and ``cell``
- Directives

  + ``cmd:def`` provide command definition
  + ``cmd:usage`` used by ``autocmd`` for command usage signatures
  + ``cell:def`` provide cell definition
  + ``cell:defprop`` provide cell property definition (used in
    :doc:`/cell/properties`)
  + ``cell:source`` used by ``autocell`` for simulation models

- Roles

  + ``cmd:ref`` link to a ``cmd:def`` with the same name
  + ``cmd:title`` same as ``cmd:ref``, but includes the short help in the text

    - ``:cmd:title:`chformal``` -> :cmd:title:`chformal`

  + ``cell:ref`` link to a ``cell:def`` with the same name
  + ``cell:title``

    - ``:cell:title:`$nex``` -> :cell:title:`$nex`

  + ``cell:prop`` link to a ``cell:defprop`` of the same name
