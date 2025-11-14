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
short sentence describing the pass, and is set in the ``Pass`` constructor, as
demonstrated here with `chformal`.

.. literalinclude:: /generated/chformal.cc
   :language: c++
   :start-at: public Pass {
   :end-before: bool formatted_help()
   :caption: ``ChformalPass()`` from :file:`passes/cmds/chformal.cc`
   :append: // ...
      } ChformalPass;

All currently available commands are listed with their ``short_help`` string
when calling `help` without arguments, and is more or less the same as the
unlisted :ref:`command index <commandindex>`.  The string is also used when
hovering over links to commands in the documentation, and in section headings
like :ref:`chformal autocmd`.

The next section shows the complete help text for the `chformal` command.  This
can be displayed locally by using ``help <command>`` (or ``yosys -h <command>``
from the command line).  The general format is to show each usage signature,
followed by a paragraph describing what the pass does, and a list of options or
flags available.  Additional arguments in the signature or option may use square
brackets (``[]``) to indicate optional parts, and angle brackets (``<>``) for
required parts.  The pipe character ``|`` may be used to indicate mutually
exclusive arguments.

.. todo:: decide on a formatting style for pass options

.. _chformal autocmd:

.. autocmd:: chformal
   :noindex:

The ``Pass::help()`` method
~~~~~~~~~~~~~~~~~~~~~~~~~~~

This is the original way to provide help text, and as of this writing is still
the most common.  The ``log()`` function should be called directly to print and
format the help text, and each line should be limited to 80 (printed)
characters.  While it is possible to provide arbitrary formatting, it is
preferred to follow the guidelines here to maintain consistency with other
passes and to assist in correct parsing and formatting during RST generation
(i.e. these docs).

The first line should always be a blank line, followed by the primary usage
signature for the command.  Each usage signature should be indented with 4
spaces, and followed by a blank line.  Each option or flag should start on a new
line indented with 4 spaces, followed by a description of the option which is
indented by a further 4 spaces, and then a blank line.  Option descriptions
typically start with lower case, and may forgo a trailing period (``.``). Where
multiple options share a description the blank line between options should be
omitted.

The ``Pass::formatted_help()`` method
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

- ``PrettyHelp::get_current()``
- ``PrettyHelp::set_group()``

  + used with ``.. autocmdgroup:: <group>``
  + can assign group and return false
  + if no group is set, will try to use ``source_location`` and assign group
    from path to source file

- return value

  + true means help content added to current ``PrettyHelp``
  + false to use ``Pass::help()``

- adding content

  + help content is a list of ``ContentListing`` nodes, each one having a type,
    body, and its own list of children ``ContentListing``\ s
  + ``PrettyHelp::get_root()`` returns the root ``ContentListing`` (``type="root"``)
  + ``ContentListing::{usage, option, codeblock, paragraph}`` each add a
    ``ContentListing`` to the current node, with type the same as the method

    * the first argument is the body of the new node
    * ``usage`` shows how to call the command (i.e. its "signature")
    * ``paragraph`` content is formatted as a paragraph of text with line breaks
      added automatically
    * ``codeblock`` content is displayed verbatim, use line breaks as desired;
      takes an optional ``language`` argument for assigning the language in RST
      output for code syntax highlighting (use ``yoscrypt`` for yosys script
      syntax highlighting)
    * ``option`` lists a single option for the command, usually starting with a
      dash (``-``); takes an optional second argument which adds a paragraph
      node as a means of description

  + ``ContentListing::open_usage`` creates and returns a new usage node, can be
    used to e.g. add text/options specific to a given usage of the command
  + ``ContentListing::open_option`` creates and returns a new option node, can
    be used to e.g. add multiple paragraphs to an option's description
  + paragraphs are treated as raw RST, allowing for inline formatting and
    references as if it were written in the RST file itself

.. literalinclude:: /generated/chformal.cc
   :language: c++
   :start-at: bool formatted_help()
   :end-before: void execute
   :caption: ``ChformalPass::formatted_help()`` from :file:`passes/cmds/chformal.cc`


Dumping command help to json
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

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


Command line rendering
~~~~~~~~~~~~~~~~~~~~~~

- if ``Pass::formatted_help()`` returns true, will call
  ``PrettyHelp::log_help()``

  + traverse over the children of the root node and render as plain text 
  + effectively the reverse of converting unformatted ``Pass::help()`` text
  + lines are broken at 80 characters while maintaining indentation (controlled
    by ``MAX_LINE_LEN`` in :file:`kernel/log_help.cc`)
  + each line is broken into words separated by spaces, if a given word starts
    and ends with backticks they will be stripped

- if it returns false it will call ``Pass::help()`` which should call ``log()``
  directly to print and format help text

  + if ``Pass::help()`` is not overridden then a default message about missing
    help will be displayed

.. literalinclude:: /generated/chformal.log
   :lines: 2-


RST generated from autocmd
~~~~~~~~~~~~~~~~~~~~~~~~~~

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

.. autocmd_rst:: chformal


Cell help
---------

- :file:`techlibs/common/simcells.v` and :file:`techlibs/common/simlib.v`
- parsed by :file:`techlibs/common/cellhelp.py`
- comments preceding cell type converted to a ``SimHelper`` struct, defined in
  :file:`kernel/register.cc`
- ``#include``\ d in :file:`kernel/register.cc`, creating a map of cell types to
  their ``SimHelper`` struct.

- ``help -cells``

  - lists all cells with their input/output ports

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
