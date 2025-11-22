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
   :name: chformal_pass
   :append:
              // ...
      } ChformalPass;

All currently available commands are listed with their ``short_help`` string
when calling `help` without arguments, and is more or less the same as the
:ref:`command index <commandindex>`.  The string is also used when hovering over
links to commands in the documentation, and in section headings like
:ref:`chformal autocmd`.

The next section shows the complete help text for the `chformal` command.  This
can be displayed locally by using `help <command>` (or ``yosys -h <command>``
from the command line).  The general format is to show each usage signature (how
the command is called), followed by a paragraph describing what the pass does,
and a list of options or flags available.  Additional arguments in the signature
or option may use square brackets (``[]``) to indicate optional parts, and angle
brackets (``<>``) for required parts.  The pipe character (``|``) may be used to
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

Warning flags
~~~~~~~~~~~~~

In order to support commands which are not intended for general use, a number of
warning flags are provided to the ``Pass`` class.  Take the
:ref:`internal_flag_example` as an example.  In the body of the constructor, we
call ``Pass::internal()`` to set the warning flag that this is an internal; i.e.
one aimed at Yosys *developers* rather than users.  Commands with the
``internal`` flag are often used for testing Yosys, and expose functionality
that would normally be abstracted.  Setting this flag also ensures that commands
will be included in :doc:`/cmd/index_internal`.

.. literalinclude:: /generated/functional/test_generic.cc
   :language: cpp
   :start-at: FunctionalTestGeneric()
   :end-at: }
   :dedent:
   :caption: `test_generic` pass constructor
   :name: internal_flag_example

The other warning flag available is ``Pass::experimental()``, also to be called
during the constructor. This should used for experimental commands that may be
unstable, unreliable, incomplete, and/or subject to change.  Experimental passes
also typically have the text ``(experimental)`` at the start of their
``short_help``, but this is not always the case.

.. todo:: should the experimental flag add ``(experimental)`` automatically?

In both cases, commands with these flags set will print additional warning text
in the help output.  Calling commands with the ``experimental`` flag set, will
also call ``log_experimental()`` with the name of the pass, providing an
additional warning any time the pass is used.

.. note::

   When testing the handling of expected error/warning messages with e.g.
   `logger`, it is possible to disable the warnings for a given experimental
   feature.  This can be done by calling Yosys with ``--experimental
   <feature>``, where ``<feature>`` is the name of the experimental pass.


The ``Pass::help()`` method
~~~~~~~~~~~~~~~~~~~~~~~~~~~

Overriding this method is the original way to provide help text, and as of this
writing is still the most common.  The ``log()`` function should be called
directly to print and format the help text, and each line should be limited to
80 (printed) characters.  While it is possible to provide arbitrary formatting,
it is preferred to follow the guidelines here to maintain consistency with other
passes and to assist in correct parsing and formatting during RST generation
(i.e. these docs).

.. note::

  It is good practice in the ``Pass::help`` method for each call to ``log()`` to
  correspond to a single line, containing exactly one ``\n`` (at the end).  This
  allows the appearance in source to match the appearance in the terminal.

The first and last lines should always be empty, followed by the primary usage
signature for the command.  Each usage signature should be indented with 4
spaces, and followed by an empty line.  Each option or flag should start on a
new line indented with 4 spaces, followed by a description of the option which
is indented by a further 4 spaces, and then an empty line. Option descriptions
typically start with lower case, and may forgo a trailing period (``.``). Where
multiple options share a description the empty line between options should be
omitted.

.. note::

   `Commands JSON`_ has more on how formatting in ``help()`` gets parsed.


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

Command groups are used when `dumping to JSON`_, so that related
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
   :name: chformal_source

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

..
   When :makevar:`ENABLE_HELP_SOURCE` is set, each ``ContentListing`` node also
   stores file path and line number of its source location.  But I think this might
   only be used when raising errors/warnings during ``autocmd``.

Command line rendering
~~~~~~~~~~~~~~~~~~~~~~

Rendering text for the command line is done by the ``Pass::help`` method.  When
this method is not overridden, the default behavior is to call
``Pass::formatted_help()``.  If this method is also left unimplemented, or the
return value is explicitly false, then a default message about missing help text
for the command is displayed.  Returning true, however, will then call
``PrettyHelp::log_help()`` to convert the formatted help content into plain
text.

.. note::

   Regardless of which help method is used, any `warning flags`_ set on the pass
   will display a message to warn the user.  These are regular messages, using
   ``log()`` rather than ``log_warning()``, meaning (for example) they will
   be suppressed by the ``-q`` command line option.

Rendering rich help text as plain text is done by traversing over all the
``ContentListing`` nodes and printing the body text.  ``usage`` nodes are
preceded by an empty line and indented one level (4 spaces).  ``option`` nodes
are also indented one level, while their children are indented an extra level (8
spaces).  Any ``codeblock`` nodes are rendered as-is at the current indentation,
with no further formatting applied.

``paragraph`` nodes are broken into words separated by spaces, and each word is
printed.  If a word would cause the current line to exceed 80 characters
(controlled by ``MAX_LINE_LEN`` in :file:`kernel/log_help.cc`), then the word
will instead be placed on a new line with the same level of indentation. Special
handling is included for words that begin and end with a backtick (`````) so
that these are stripped when printing to the command line.  Compare
:ref:`chformal_help` below with the :ref:`chformal autocmd` above.  The content
is still the same, but for the command line it uses a fixed width.

.. todo:: spaces in backticks (``assert(...)`` vs ````assert(s_eventually ...)````)

.. literalinclude:: /generated/chformal.log
   :lines: 2-
   :name: chformal_help
   :caption: Command line output for `help chformal`


Cell help
---------

Unlike commands, cell help text is generated at compile time, and is not
affected by platform or compile flags.  This also means that it is not possible
to provide help content for custom cell types in plugins or technology
libraries.

Two verilog simulation libraries provide models for all built-in cell types.
These are defined in :file:`techlibs/common/simcells.v` (for
:doc:`/cell/index_gate`) and :file:`techlibs/common/simlib.v` (for
:doc:`/cell/index_word`).  Each model is preceded by a structured comment block,
formatted as either :ref:`v1` or :ref:`v2`.  These comment blocks are processed
by a python script, :file:`techlibs/common/cellhelp.py`, to generate the help
content used in :file:`kernel/register.cc`.

.. note::

  Each verilog module (and its comment block) is parsed into a C++ ``dict``,
  mapping the cell type (the name of the verilog module) to a ``SimHelper``
  struct in :file:`kernel/register.cc` with ``#include``\ s. Calling `help
  <celltype>` then retrieves the corresponding ``SimHelper`` and displays the
  help text contained.

Calling `help -cells` will list all built-in cell types with their input/output
ports.  There is again an unlisted :ref:`cell index <cellindex>` which shows all
cell types with their title.  Unlike commands, providing a title is optional,
and only available with `v2`_ formatting, so most just use the name of the cell
(qualified with the containing group).  It is also possible to display the
verilog simulation model by calling `help <celltype>+`.

.. _v1:

v1 (default)
~~~~~~~~~~~~

As mentioned previously, the verilog simulation models are preceded by a
structured comment block.  Each line starting with ``//-`` is added to the
description of the next verilog module.  Non-empty lines must have a space after
the dash before text, and should be limited to 80 characters (84 including the
``//-``).  The description is rendered to the terminal as-is when calling `help
<celltype>`, while the web docs will render it as text, with empty lines being
used to separate paragraphs.

..
   Descriptions can extend into the verilog module itself, including *all* comment
   lines that start with a dash prior to the ``endmodule``.  However, everything in
   the ``module .. endmodule`` block is considered source code, so this is not
   recommended.

.. note::

   Most of the legacy cell descriptions include a signature line (``//-
   $<celltype> (<ports>)``).  More recent versions of the help generation will
   automatically produce this signature from the verilog declaration, making
   this an optional inclusion.  Note that if a signature line *is* included, it
   *must* start with at least 4 spaces (not tabs), and include one empty line
   (``//-``) before and after.

Each cell type must also be assigned a group, failing to do so will produce an
error.  This can be done by adding ``//* group <cellgroup>`` anywhere in the
comment block.  As with commands, the group determines where the cell appears in
the Sphinx documentation, but does not otherwise impact the output of `help`. As
with commands, there is no warning produced if cells are assigned a group which
is not used in the documentation.  Make sure to check :file:`docs/source/cell`
for the groups currently available.

For the cell models in :file:`techlibs/common/simcells.v`, it is possible to
provide a truth table at the end of the cell description which is rendered in
sphinx docs as a literal code block.  We can look at the :ref:`NOT_module` to
see this in action.

.. literalinclude:: /generated/simcells._NOT_.v
   :language: verilog
   :start-at: //-
   :end-at: module \$_NOT_
   :name: NOT_module
   :caption: `$_NOT_` cell comment block from :file:`techlibs/common/simcells.v`

..
   v1 descriptions in :file:`techlibs/common/simcells.v` have their version
   unconditionally changed to ``2a`` to facilitate the truth table rendering,
   making use of the v2 handling of codeblocks with ``::``.  This also means A.
   using ``::`` on its own in a v1 (gate-level) description should be avoided, and
   B. *all* text after the ``"Truth table:"`` line is included in the codeblock.


.. _v2:

v2 (more expressive)
~~~~~~~~~~~~~~~~~~~~

Fields can be directly assigned with a ``//* <name> <value>`` comment line.  We
saw this in the `v1`_ format with the group, but this is actually possible with
*all* fields of the ``SimHelper`` struct.  In order to use the extra fields,
``ver`` must be explicitly set as ``2``.  The extra fields available are as
follows, with an example provided by the :ref:`nex_module`.

- title
   A short title for the cell, equivalent to ``short_help`` in commands.
   Rendered before the description and when hovering over links in
   documentation.

- tags
   A space-separated list of :doc:`/cell/properties`.  Not used in `help`
   output, but provided when dumping to JSON and in the Sphinx docs.

.. literalinclude:: /generated/simlib.nex.v
   :language: verilog
   :name: nex_module
   :caption: `$nex` cell comment block from :file:`techlibs/common/simlib.v`

.. warning::

   While it is possible to assign values to any of the ``SimHelper`` fields,
   some fields are automatically assigned and explicitly setting them may result
   in errors, or discarding of the assigned value.  These fields are the name,
   ports, code, source, and desc.

The cell description is provided in the same way as in `v1`_, with each line
starting with a ``//-``.  When generating the Sphinx documentation, the cell
description is interpreted as raw RST.  This allows both in-line formatting like
linking to commands or passes using backticks (`````), and literal code blocks
with the ``::`` marker as in the following example:

.. tab:: Verilog comment

   .. code-block:: verilog

      //- text
      //- ::
      //-
      //-    monospaced text
      //-
      //-        indentation and line length will be preserved, giving a scroll bar if necessary for the browser window
      //-
      //- more text

.. tab:: formatted output

   text
   ::

      monospaced text

         indentation and line length will be preserved, giving a scroll bar if necessary for the browser window

   more text

Note that the empty line after the ``::`` and before the text continues are
required, as is the indentation before the literal contents.  When rendering to
the terminal with `help <celltype>`, the ``::`` line will be ignored, while
Sphinx displays the section verbatim like shown.

.. todo:: in line formatting for web docs isn't exclusive to v2,

   but it does raise the question of if we should be doing something to prevent
   v1 descriptions being treated as raw RST.


Dumping to JSON
---------------

Once compiled, Yosys is able to dump both the internal command and cell
libraries to a machine-readable JSON file.  Primarily intended for building this
documentation (more on that in the next section), this feature is not advertised
within Yosys itself, and can be done with `help -dump-cmds-json <cmds.json>` and
`help -dump-cells-json <cells.json>` respectively.

Both JSON files are formatted very similarly, containing a single object.  The
object has a ``version`` field which disambiguates between the two, a
``generator`` field which contains the Yosys version string used, a ``groups``
object which maps each group to the list of commands/cells in that group, and
finally a ``cmds`` or ``cells`` object which maps each command/cell to its help
content.

.. TODO:: Document how things get to Read the Docs

   - :file:`.github/workflows/prepare-docs.yml`
   - github job compiles Yosys (with Verific)
   - dumps JSON
   - dumps program usage output for :doc:`/cmd_ref` and
     :doc:`/appendix/auxprogs`
   - runs examples, producing logs and images
   - copies (some) source files for inclusion
   - compresses and uploads artifact
   - conditionally triggers RTDs to build
   - ``rtds_action`` extension

Commands JSON
~~~~~~~~~~~~~

Lets take a look at :ref:`chformal_json` as an example.  We can see the bulk of
the object is taken up by the ``content`` field, which contains all the
``ContentListing`` nodes we added in :ref:`the formatted_help method for
chformal <chformal_source>`, maintaining the structure of those nodes.  The
command's ``short_help`` is given in the ``title`` field, with other fields for
the `Warning flags`_, source location, source function, and corresponding group
(either implicit or explicit).

.. literalinclude:: /generated/cmds.json
   :language: json
   :start-at: "chformal": {
   :end-at: "internal_flag": false
   :append: }
   :dedent:
   :caption: `chformal` in generated :file:`cmds.json`
   :name: chformal_json

Every command registered in Yosys (including those from currently installed
plugins) has a corresponding object in the JSON dump.  For commands where
``Pass::formatted_help()`` is unimplemented or returns false, ``ContentListing``
nodes will be generated by parsing the unformatted ``Pass::help()`` output. This
is largely the same as `Command line rendering`_ but in reverse, with a few
simple rules to try convert between raw text and the different node types.

To be parsed as a ``usage`` node, the current line:
  + must start with the name of the command (case sensitive), followed by a
    space or a new line;
  + may have up to four characters of whitespace as indentation;
  + must be the first non-empty line, preceded by two empty lines, or
    immediately following another usage signature with the same indentation.

Any lines immediately after a usage signature which is indented more than the
signature will be appended to the usage signature.  This allows for breaking
arguments across lines in the terminal output while still producing a single
``usage`` node.

.. code-block:: cpp
  :caption: Example code for a command with multiple usage signatures

  log("\n");
  log("    command\n");
  log("    command -argument\n");
  log("            -another argument\n");
  log("\n");
  log("\n");
  log("command description.\n"); // not a signature because it is dedented
  log("\n");
  log("\n");
  log("    command -different argument\n");
  log("\n");

If a line is indented and starts with a dash (``-``), and does not immediately
follow a usage signature, it is parsed as an ``option`` node.  Anything else is
parsed as a ``codeblock`` and added to either the root node or the current
option depending on the indentation.  This allows yosys script syntax
highlighting for (most) options, while still respecting help content which
relies on the fixed-width rendering.

To enable syntax highlighting in synthesis command scripts, if the final block
of help output starts with the string ``"The following commands are executed by
this synthesis command:\n"``, then the rest of the code block is formatted as
``yoscrypt`` (e.g. `synth_ice40`).  The caveat here is that if the ``script()``
calls ``run()`` on any commands *prior* to the first ``check_label`` then the
auto detection will break and revert to unformatted code (e.g.
`synth_fabulous`).


Cells JSON
~~~~~~~~~~

Dumping the cell help contents to JSON follows a very similar format as the
``SimHelper`` struct.  The main difference is that there is no ``ver`` or
``group`` field, and the ``tags`` have become ``properties``.  Each cell type
also has a corresponding ``CellType`` struct defined in
:file:`kernel/celltypes.h` which we now have access to.  This allows us to
distinguish which ports are inputs and which are outputs, as well as some extra
property flags.  The :ref:`nex_json` is reproduced here to show this
transformation.

.. literalinclude:: /generated/cells.json
   :language: json
   :start-at: "$nex": {
   :end-at: },
   :caption: `$nex` in generated :file:`cells.json`
   :name: nex_json


Working with Sphinx
-------------------

This documentation is built on Sphinx using `reStructuredText`_.  To support the
rich documentation of commands and cells in Yosys, as well as the Yosys
scripting language and RTLIL, we use some custom extensions and will touch on
those here.

.. _reStructuredText: https://docutils.sourceforge.io/rst.html

Sphinx uses `Pygments`_ for syntax highlighting code blocks, for which we
provide to additional lexers. The first of these is ``RTLIL`` for the
:doc:`/yosys_internals/formats/rtlil_rep`, and is exclusive to the Yosys docs.
The second lexer, ``yoscrypt``, is for :doc:`/getting_started/scripting_intro`
and is available across all of the YosysHQ docs through `furo-ys`_, our custom
fork of the `furo`_ theme for Sphinx.  These languages are automatically
associated with the ``.il`` and ``.ys`` file extensions respectively, and can be
selected for use in any ``literalinclude`` or ``code-block`` segments.

.. _Pygments: https://pygments.org/
.. _furo-ys: https://github.com/YosysHQ/furo-ys/
.. _furo: https://github.com/pradyunsg/furo

To simplify inline Yosys script syntax highlighting, these docs provide the
``yoscrypt`` role.  This role renders (e.g.) ``:yoscrypt:`chformal -remove```
into :yoscrypt:`chformal -remove`.  For linking to command and cell
documentation, we also use a default role of ``autoref``.  Any text in single
backticks without an explicit role will be assigned this one.  We've already
seen this being used above in the help text for `chformal` and `$nex` (which
were themselves written as ```chformal``` and ```$nex``` respectively).  

By using the `autodoc extension`_ and two custom `Sphinx Domains`_ (more on them
later), ``autoref`` is able to produce links to any commands or cells available
in Yosys.  So long as there are no spaces in the text, and it doesn't begin with
a dash (``-``), it will try to convert it to a link.  If the text begins with
``$`` then it will use the ``cell:ref`` role, otherwise it will use ``cmd:ref``.
Let's take a look at some examples:

.. _Sphinx Domains: https://www.sphinx-doc.org/en/master/usage/domains/index.html
.. _autodoc extension: https://www.sphinx-doc.org/en/master/usage/extensions/autodoc.html

.. tab:: reStructuredText

   .. literalinclude:: formatting_sample.txt
      :language: reStructuredText
      :start-after: .. 1
      :end-before: .. 2

.. tab:: formatted output

   .. include:: formatting_sample.txt
      :start-after: .. 1
      :end-before: .. 2

Notice how referencing `chformal` also puts the command name in an inline code
block.  This is automatically done thanks to the use of `Sphinx Domains`_ and
helps to distinguish commands (and cells) from other types of links.  The
``autoref`` role also works with two words, if the first one is "help":

.. tab:: reStructuredText

   .. literalinclude:: formatting_sample.txt
      :language: reStructuredText
      :start-after: .. 2
      :end-before: .. 3

.. tab:: formatted output

   .. include:: formatting_sample.txt
      :start-after: .. 2
      :end-before: .. 3

And if the text begins with a dash, or doesn't match the "help" formatting, it
will fallback to formatting as inline yoscrypt.

.. tab:: reStructuredText

   .. literalinclude:: formatting_sample.txt
      :language: reStructuredText
      :start-after: .. 3
      :end-before: .. 4

.. tab:: formatted output

   .. include:: formatting_sample.txt
      :start-after: .. 3
      :end-before: .. 4

Using autodoc
~~~~~~~~~~~~~

The vast majority of command and cell help content in these docs is done with
the the `autodoc extension`_.  By generating Sphinx documentation from our JSON
dumps of commands and cells, not only are we able to write the help content once
and have it available both in Yosys itself and online, we also ensure that any
code changes or additions are automatically propagated to the web docs.

.. note::

   We are focusing on the ``autocmd`` directive here because it is easier to
   demonstrate.  In practice we don't really use it directly outside of this
   page, and instead make use of the ``autocmdgroup`` directive.  By providing
   the ``:members:`` option, this is the same as calling ``autocmd`` for each
   command in the group and means that any new commands are added automatically.

Now let's take a look at the :ref:`chformal_rst` behind :ref:`chformal autocmd`.
This conversion is done by the ``YosysCmdDocumenter`` class in
:file:`docs/util/cmd_documenter.py`.  We can see all of our ``paragraph`` and
``option`` nodes from :ref:`ChformalPass::formatted_help() <chformal_source>`
have made it through, as has the ``short_help`` from our :ref:`ChformalPass()
constructor <chformal_pass>`.  The heading will be rendered as a subheading of
the most recent heading (notice how the `chformal` help content above is listed
under `Command help`_ in the table of contents).

.. _chformal_rst:

.. autocmd_rst:: chformal

To support cross references with the ``cmd:ref`` role, we see everything is
under the ``cmd:def`` directive.  The ``:title:`` option is what controls the
text that appears when hovering over the `chformal` link, and when using the
``cmd:title`` role.  For commands with `warning flags`_, a ``.. warning`` block
is added to the generated RST before any of the help content.  This is the same
`warning admonition`_ that we've seen elsewhere on this page.  For commands with
no ``source_location``, the ``.. seealso`` block at the bottom will instead link
to :doc:`/cmd/index_other`.

.. _warning admonition: https://pradyunsg.me/furo/reference/admonitions/#warning

.. hint::

   The :ref:`chformal autocmd` on this page uses the ``:noindex:`` option so
   that references to `chformal` link to the :doc:`/cmd_ref` instead of this
   page.

For documenting cells we have ``autocell`` and ``autocellgroup``, which function
pretty similarly to their command-based counter parts, ``autocmd`` and
``autocmdgroup``.  These directives are provided by the ``YosysCellDocumenter``
in :file:`docs/util/cell_documenter.py`.  Like with `help <celltype>+`, we are
able to include verilog simulation models in our ``autodoc`` with the
``:source:`` option.  We can then also include line numbers by adding
``:linenos:``, which is very useful when trying to find the source code being
referenced.

.. todo:: would be nice to get a ``.. autocell:: $nex``

   like we did with `chformal autocmd`_, but it doesn't seem to like the
   ``:noindex:`` option, or using ``:source:`` without it being
   ``binary::$nex``.

.. todo:: cells can have properties (:ref:`propindex`)

.. note::

   For :ref:`showing autocmd generated rst <chformal_rst>` on this page, we also
   have the ``autocmd_rst`` directive.  This is not used anywhere else in the
   documentation, but it's mentioned here since we're already deep in the weeds
   of how these docs are made.

Our custom Sphinx domains
~~~~~~~~~~~~~~~~~~~~~~~~~

To round out this document about documentation, let's take a brief look at our
custom Sphinx domains and what they provide.  As you might expect from `Using
autodoc`_, these docs come with a domain for Yosys commands (``cmd``), and a
domain for built-in cells (``cell``).  These are both provided in
:file:`docs/util/custom_directives.py`.  From these domains we have the
following directives (``.. <directive>::`` in RST):

- ``cmd:def`` provide command definition,
- ``cmd:usage`` used by ``autocmd`` for command usage signatures,
- ``cell:def`` provide cell definition,
- ``cell:defprop`` provide cell property definition (used in
  :doc:`/cell/properties`), and
- ``cell:source`` used by ``autocell`` for simulation models.

For general documentation, it should not be necessary to interact with any of
these directives.  Rather, everything should be accomplished through the use of
``autocmdgroup`` and ``autocellgroup``.  We also have a few roles provided
(``:<role>:`<command or cell>``` in RST):

- ``cmd:ref`` link to a ``cmd:def`` with the same name
- ``cmd:title`` same as ``cmd:ref``, but includes the short help in the text
- ``cell:ref`` link to a ``cell:def`` with the same name
- ``cell:title`` same as ``cell:ref``, but includes the title in the text
- ``cell:prop`` link to a ``cell:defprop`` of the same name

For the ``<domain>:ref`` roles it's almost always easier to just not specify the
role; that's why ``autoref`` is there.  And since all of the built-in cell types
start with ``$``, it's very easy to distinguish between a ``cmd:ref`` and a
``cell:ref``.  When introducing a command it can be useful to quickly insert a
short description of it, so ``cmd:title`` sees a fair bit of use across the
documentation; particularly when it comes to the user-facing sections:

.. TODO:: is this the first time we mention the user/developer split?

.. tab:: reStructuredText

   .. literalinclude:: formatting_sample.txt
      :language: reStructuredText
      :start-after: .. 4
      :end-before: .. 5

.. tab:: formatted output

   .. include:: formatting_sample.txt
      :start-after: .. 4
      :end-before: .. 5

Since only a small subset of cells provide titles (at the time of writing),
``cell:title`` is much less reliable, and more likely to give something that
isn't intended for the reader to see (like with `$_NOT_` in the above example).
The existence of ``cell:title`` is mostly an artifact of the ``CellDomain``
being a subclass of the ``CommandDomain``.

.. warning::

   Because of how Sphinx caches domains (and/or because of how the
   ``CommandDomain`` is setup), rebuilding pages with ``autocmdgroup`` or
   ``autocellgroup`` directives can result in duplicate definitions on the
   :ref:`command <commandindex>` and :ref:`cell <cellindex>` indices.  A ``make
   clean`` or ``rm -rf docs/build`` will resolve this.  The online documentation
   is not affected by this, since it always performs a clean build.