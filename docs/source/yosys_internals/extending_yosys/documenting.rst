Documenting Yosys
=================

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

A brief description
~~~~~~~~~~~~~~~~~~~

In conjunction with the name of the pass, the ``Pass::short_help`` is likely the
first thing people look at when trying to find a command that does what they
want.  It should be a short sentence describing *what* the pass does, not *how*
it is used, and is set in the ``Pass`` constructor with the name of the pass, as
demonstrated here with `chformal`.

.. literalinclude:: /generated/chformal.cc
   :language: c++
   :start-at: public Pass {
   :end-at: ChformalPass()
   :caption: ``ChformalPass()`` from :file:`passes/cmds/chformal.cc`
   :name: chformal_pass
   :append:
              // ...
      } ChformalPass;

This brief description is always provided with the name of the pass, as in
:cmd:title:`chformal`, so there is no need to repeat the name, start with a
capital letter, or end with a period (``.``).

.. seealso::

   :ref:`short_help_use`

Warning flags
~~~~~~~~~~~~~

In order to support commands which are not intended for general use, a number of
warning flags are provided to the ``Pass`` class.  Take the
:ref:`internal_flag_example` as an example.  In the body of the constructor, we
call ``Pass::internal()`` to set the warning flag that this is an internal; i.e.
one aimed at Yosys *developers* rather than users.  Commands with the
``internal`` flag are often used for testing Yosys, and expose functionality
that would normally be abstracted.

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

.. seealso::

   :ref:`warning_flages_use`

Usage guidance
~~~~~~~~~~~~~~

The bulk of a command's help text is structured around how it is used, it's
usage signatures (how the command is called), and available options.  Let's take
a look at the :ref:`chformal_help`.  The first thing we see is the primary usage
signature for the command, followed by a paragraph which expands on and
reiterates the brief description in the ``short_help``.

.. todo:: spaces in backticks (``assert(...)`` vs ````assert(s_eventually ...)````)

.. literalinclude:: /generated/chformal.log
   :lines: 2-
   :name: chformal_help
   :caption: Command line output for `help chformal`


.. TODO:: usage (and option) formatting guidelines

   Additional arguments in the signature or option may use square brackets
   (``[]``) to indicate optional parts, and angle brackets (``<>``) for required
   parts.  The pipe character (``|``) may be used to indicate mutually exclusive
   arguments.

.. note::

   Remember that when using ``Frontend`` and ``Backend`` the pass name will be
   be prefixed with ``read_`` or ``write_`` respectively.  Usage signatures must
   match the pass name available in commands/scripts, which is available as
   ``Pass::pass_name``.

.. todo:: decide on a formatting style for pass options

.. todo:: do we need to warn about line length for usage nodes?

.. TODO:: do we discuss the selection argument here?

.. todo:: figure out ``[selection]`` alternatives (``[module_selection]``\ ?)

All available options (or flags) for the usage should be listed, along with a
description of the option.  Options may be grouped together, and a single
desription can be given for multiple options.  Longer descriptions may be broken
into paragraphs.  Similar to the ``short_help``, if a description is only a
single sentence it will typically start with lower case and forgo the trailing
period.  If the same option (or group of options) is available for multiple
usage signatures, they only need to be listed the first time.

The ``Pass::formatted_help()`` method
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. TODO:: fixup and figure out where details about ````` usage goes

Rich help text is provided with the ``formatted_help`` method, and passes using
this functionality should ``#include "kernel/log_help.h"``.

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
text with line breaks added automatically; the argument itself shouldn't contain
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

.. note::

   Many older passes do not yet use the ``formatted_help`` method, and it
   continues to be opt-in.  To learn more about the original way of providing
   help, its limitations, and how it is processed for the web, check out
   :ref:`pass_help`.

Setting a command group
~~~~~~~~~~~~~~~~~~~~~~~

Command groups are used so that related commands can be presented together in
documentation.  For example, all of the formal commands (which `chformal` is one
of) are listed under :doc:`/cmd/index_formal`.  By default, commands are grouped
by their source location, such that the group is the same as the path to the
source file.  

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
not share a common source location (e.g. the ``formal`` group), separating
commands in a shared directory (e.g. the ``passes/status`` group are all in the
``passes/cmds`` directory), and ensuring that commands are still grouped when
location tracking is disabled.

Cell help
---------

Unlike commands, cell help text is generated at compile time, and is not
affected by platform or compile flags.  This also means that it is not possible
to provide help content for custom cell types in plugins or technology
libraries.

Structured comment blocks
~~~~~~~~~~~~~~~~~~~~~~~~~

Two verilog simulation libraries provide models for all built-in cell types.
These are defined in :file:`techlibs/common/simcells.v` (for
:doc:`/cell/index_gate`) and :file:`techlibs/common/simlib.v` (for
:doc:`/cell/index_word`).  Each model is preceded by a structured comment block,
and is parsed (along with the verilog module itself) into a ``SimHelper``
struct.  The :ref:`nex_module` shows an example of this comment block.

.. literalinclude:: /generated/simlib.nex.v
   :language: verilog
   :name: nex_module
   :caption: `$nex` cell comment block from :file:`techlibs/common/simlib.v`

..
   Comment blocks can extend into the verilog module itself, including *all* comment
   lines that start with a dash prior to the ``endmodule``.  However, everything in
   the ``module .. endmodule`` block is considered source code, so this is not
   recommended.

Each line starting with ``//-`` is added to the description of the next verilog
module.  Other fields of the ``SimHelper`` struct can be directly assigned with
a ``//* <name> <value>`` comment line.  The fields available are as follows:

.. TODO:: consider reducing details about rendering and json

   or at least be consistent with commands

- group
   The group the cell belongs to.  Not setting this will produce an error.

- ver
   Formatting version, must be set to ``2`` to use the following fields.

- title
   A short title for the cell, equivalent to ``short_help`` in commands.
   Rendered before the description and when hovering over links in
   documentation.

- tags
   A space-separated list of :doc:`/cell/properties`.  Not used in `help`
   output, but provided when dumping to JSON and in the Sphinx docs.

.. warning::

   While it is possible to assign values to any of the ``SimHelper`` fields,
   some fields are automatically assigned and explicitly setting them may result
   in errors, or discarding of the assigned value.  These fields are the name,
   ports, code, source, and desc.

Describing cell types
~~~~~~~~~~~~~~~~~~~~~

.. TODO:: more about what the description should include

Non-empty lines must have a space after the dash before text, and should be
limited to 80 characters (84 including the ``//-``).  When rendering for the
web, cell descriptions are formatted as paragraphs.  To provide literal code
blocks instead, which preserve indentation and line length, the ``::`` marker
can be used as in the following example:

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

.. TODO:: how to check what metadata for cells might be applicable
