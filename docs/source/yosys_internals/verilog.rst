Notes on Verilog support in Yosys
=================================

.. TODO:: how much of this is specific to the read_verilog and should be in :doc:`/yosys_internals/flow/verilog_frontend`?

Unsupported Verilog-2005 Features
---------------------------------

The following Verilog-2005 features are not supported by
Yosys and there are currently no plans to add support
for them:

- Non-synthesizable language features as defined in
	IEC 62142(E):2005 / IEEE Std. 1364.1(E):2002

- The ``tri``, ``triand`` and ``trior`` net types

- The ``config`` and ``disable`` keywords and library map files


Verilog Attributes and non-standard features
--------------------------------------------

- The ``full_case`` attribute on case statements is supported (also the
  non-standard ``// synopsys full_case`` directive)

- The ``parallel_case`` attribute on case statements is supported (also the
  non-standard ``// synopsys parallel_case`` directive)

- The ``// synopsys translate_off`` and ``// synopsys translate_on`` directives
  are also supported (but the use of ``` `ifdef .. `endif ``` is strongly
  recommended instead).

- The ``nomem2reg`` attribute on modules or arrays prohibits the automatic early
  conversion of arrays to separate registers. This is potentially dangerous.
  Usually the front-end has good reasons for converting an array to a list of
  registers. Prohibiting this step will likely result in incorrect synthesis
  results.

- The ``mem2reg`` attribute on modules or arrays forces the early conversion of
  arrays to separate registers.

- The ``nomeminit`` attribute on modules or arrays prohibits the creation of
  initialized memories. This effectively puts ``mem2reg`` on all memories that
  are written to in an ``initial`` block and are not ROMs.

- The ``nolatches`` attribute on modules or always-blocks prohibits the
  generation of logic-loops for latches. Instead all not explicitly assigned
  values default to x-bits. This does not affect clocked storage elements such
  as flip-flops.

- The ``nosync`` attribute on registers prohibits the generation of a storage
  element. The register itself will always have all bits set to 'x' (undefined).
  The variable may only be used as blocking assigned temporary variable within
  an always block. This is mostly used internally by Yosys to synthesize Verilog
  functions and access arrays.

- The ``nowrshmsk`` attribute on a register prohibits the generation of
  shift-and-mask type circuits for writing to bit slices of that register.

- The ``onehot`` attribute on wires mark them as one-hot state register. This is
  used for example for memory port sharing and set by the fsm_map pass.

- The ``blackbox`` attribute on modules is used to mark empty stub modules that
  have the same ports as the real thing but do not contain information on the
  internal configuration. This modules are only used by the synthesis passes to
  identify input and output ports of cells. The Verilog backend also does not
  output blackbox modules on default. `read_verilog`, unless called with
  ``-noblackbox`` will automatically set the blackbox attribute on any empty
  module it reads.

- The ``noblackbox`` attribute set on an empty module prevents `read_verilog`
  from automatically setting the blackbox attribute on the module.

- The ``whitebox`` attribute on modules triggers the same behavior as
  ``blackbox``, but is for whitebox modules, i.e. library modules that contain a
  behavioral model of the cell type.

- The ``lib_whitebox`` attribute overwrites ``whitebox`` when `read_verilog` is
  run in ``-lib`` mode. Otherwise it's automatically removed.

- The ``dynports`` attribute is used by the Verilog front-end to mark modules
  that have ports with a width that depends on a parameter.

- The ``hdlname`` attribute is used by some passes to document the original
  (HDL) name of a module when renaming a module. It should contain a single
  name, or, when describing a hierarchical name in a flattened design, multiple
  names separated by a single space character.

- The ``keep`` attribute on cells and wires is used to mark objects that should
  never be removed by the optimizer. This is used for example for cells that
  have hidden connections that are not part of the netlist, such as IO pads.
  Setting the ``keep`` attribute on a module has the same effect as setting it
  on all instances of the module.

- The ``keep_hierarchy`` attribute on cells and modules keeps the `flatten`
  command from flattening the indicated cells and modules.

- The `gate_cost_equivalent` attribute on a module can be used to specify
  the estimated cost of the module as a number of basic gate instances. See
  the help message of command `keep_hierarchy` which interprets this
  attribute.

- The ``init`` attribute on wires is set by the frontend when a register is
  initialized "FPGA-style" with ``reg foo = val``. It can be used during
  synthesis to add the necessary reset logic.

- The ``top`` attribute on a module marks this module as the top of the design
  hierarchy. The `hierarchy` command sets this attribute when called with
  ``-top``. Other commands, such as `flatten` and various backends use this
  attribute to determine the top module.

- The ``src`` attribute is set on cells and wires created by to the string
  ``<hdl-file-name>:<line-number>`` by the HDL front-end and is then carried
  through the synthesis. When entities are combined, a new \|-separated string
  is created that contains all the strings from the original entities.

- The ``defaultvalue`` attribute is used to store default values for module
  inputs. The attribute is attached to the input wire by the HDL front-end when
  the input is declared with a default value.

- The ``parameter`` and ``localparam`` attributes are used to mark wires that
  represent module parameters or localparams (when the HDL front-end is run in
  ``-pwires`` mode).

- Wires marked with the ``hierconn`` attribute are connected to wires with the
  same name (format ``cell_name.identifier``) when they are imported from
  sub-modules by `flatten`.

- The ``clkbuf_driver`` attribute can be set on an output port of a blackbox
  module to mark it as a clock buffer output, and thus prevent `clkbufmap` from
  inserting another clock buffer on a net driven by such output.

- The ``clkbuf_sink`` attribute can be set on an input port of a module to
  request clock buffer insertion by the `clkbufmap` pass.

- The ``clkbuf_inv`` attribute can be set on an output port of a module with the
  value set to the name of an input port of that module.  When the `clkbufmap`
  would otherwise insert a clock buffer on this output, it will instead try
  inserting the clock buffer on the input port (this is used to implement clock
  inverter cells that clock buffer insertion will "see through").

- The ``clkbuf_inhibit`` is the default attribute to set on a wire to prevent
  automatic clock buffer insertion by `clkbufmap`. This behaviour can be
  overridden by providing a custom selection to `clkbufmap`.

- The ``invertible_pin`` attribute can be set on a port to mark it as invertible
  via a cell parameter.  The name of the inversion parameter is specified as the
  value of this attribute.  The value of the inversion parameter must be of the
  same width as the port, with 1 indicating an inverted bit and 0 indicating a
  non-inverted bit.

- The ``iopad_external_pin`` attribute on a blackbox module's port marks it as
  the external-facing pin of an I/O pad, and prevents `iopadmap` from inserting
  another pad cell on it.

- The module attribute ``abc9_lut`` is an integer attribute indicating to `abc9`
  that this module describes a LUT with an area cost of this value, and
  propagation delays described using ``specify`` statements.

- The module attribute ``abc9_box`` is a boolean specifying a black/white-box
  definition, with propagation delays described using ``specify`` statements,
  for use by `abc9`.

- The port attribute ``abc9_carry`` marks the carry-in (if an input port) and
  carry-out (if output port) ports of a box. This information is necessary for
  `abc9` to preserve the integrity of carry-chains. Specifying this attribute
  onto a bus port will affect only its most significant bit.

- The module attribute ``abc9_flop`` is a boolean marking the module as a
  flip-flop. This allows `abc9` to analyse its contents in order to perform
  sequential synthesis.

- The frontend sets attributes ``always_comb``, ``always_latch`` and
  ``always_ff`` on processes derived from SystemVerilog style always blocks
  according to the type of the always. These are checked for correctness in
  ``proc_dlatch``.

- The cell attribute ``wildcard_port_conns`` represents wildcard port
  connections (SystemVerilog ``.*``). These are resolved to concrete connections
  to matching wires in `hierarchy`.

- In addition to the ``(* ... *)`` attribute syntax, Yosys supports the
  non-standard ``{* ... *}`` attribute syntax to set default attributes for
  everything that comes after the ``{* ... *}`` statement. (Reset by adding an
  empty ``{* *}`` statement.)

- In module parameter and port declarations, and cell port and parameter lists,
  a trailing comma is ignored. This simplifies writing Verilog code generators a
  bit in some cases.

- Modules can be declared with ``module mod_name(...);`` (with three dots
  instead of a list of module ports). With this syntax it is sufficient to
  simply declare a module port as 'input' or 'output' in the module body.

- When defining a macro with ``\`define``, all text between triple double quotes
  is interpreted as macro body, even if it contains unescaped newlines. The
  triple double quotes are removed from the macro body. For example:

.. code-block:: verilog

      `define MY_MACRO(a, b) """
         assign a = 23;
         assign b = 42;
      """

- The attribute ``via_celltype`` can be used to implement a Verilog task or
  function by instantiating the specified cell type. The value is the name of
  the cell type to use. For functions the name of the output port can be
  specified by appending it to the cell type separated by a whitespace. The body
  of the task or function is unused in this case and can be used to specify a
  behavioral model of the cell type for simulation. For example:

.. code-block:: verilog

      module my_add3(A, B, C, Y);
        parameter WIDTH = 8;
        input [WIDTH-1:0] A, B, C;
        output [WIDTH-1:0] Y;
        ...
      endmodule

      module top;
        ...
        (* via_celltype = "my_add3 Y" *)
        (* via_celltype_defparam_WIDTH = 32 *)
        function [31:0] add3;
          input [31:0] A, B, C;
          begin
            add3 = A + B + C;
          end
        endfunction
        ...
      endmodule

- The ``wiretype`` attribute is added by the verilog parser for wires of a
  typedef'd type to indicate the type identifier.

- Various ``enum_value_{value}`` attributes are added to wires of an enumerated
  type to give a map of possible enum items to their values.

- The ``enum_base_type`` attribute is added to enum items to indicate which enum
  they belong to (enums -- anonymous and otherwise -- are automatically named
  with an auto-incrementing counter). Note that enums are currently not strongly
  typed.

- A limited subset of DPI-C functions is supported. The plugin mechanism (see
  ``help plugin``) can be used to load .so files with implementations of DPI-C
  routines. As a non-standard extension it is possible to specify a plugin alias
  using the ``<alias>:`` syntax. For example:

.. code-block:: verilog

      module dpitest;
        import "DPI-C" function foo:round = real my_round (real);
        parameter real r = my_round(12.345);
      endmodule

.. code-block::

      $ yosys -p 'plugin -a foo -i /lib/libm.so; read_verilog dpitest.v'

- Sized constants (the syntax ``<size>'s?[bodh]<value>``) support constant
  expressions as ``<size>``. If the expression is not a simple identifier, it
  must be put in parentheses. Examples: ``WIDTH'd42``, ``(4+2)'b101010``

- The system tasks ``$finish``, ``$stop`` and ``$display`` are supported in
  initial blocks in an unconditional context (only if/case statements on
  expressions over parameters and constant values are allowed). The intended use
  for this is synthesis-time DRC.

- There is limited support for converting ``specify`` .. ``endspecify``
  statements to special ``$specify2``, ``$specify3``, and ``$specrule`` cells,
  for use in blackboxes and whiteboxes. Use ``read_verilog -specify`` to enable
  this functionality. (By default these blocks are ignored.)

- The ``reprocess_after`` internal attribute is used by the Verilog frontend to
  mark cells with bindings which might depend on the specified instantiated
  module. Modules with such cells will be reprocessed during the `hierarchy`
  pass once the referenced module definition(s) become available.

- The ``smtlib2_module`` attribute can be set on a blackbox module to specify a
  formal model directly using SMT-LIB 2. For such a module, the
  ``smtlib2_comb_expr`` attribute can be used on output ports to define their
  value using an SMT-LIB 2 expression. For example:

.. code-block:: verilog

      (* blackbox *)
      (* smtlib2_module *)
      module submod(a, b);
        input [7:0] a;
        (* smtlib2_comb_expr = "(bvnot a)" *)
        output [7:0] b;
      endmodule

Non-standard or SystemVerilog features for formal verification
--------------------------------------------------------------

- Support for ``assert``, ``assume``, ``restrict``, and ``cover`` is enabled
  when `read_verilog` is called with ``-formal``.

- The system task ``$initstate`` evaluates to 1 in the initial state and to 0
  otherwise.

- The system function ``$anyconst`` evaluates to any constant value. This is
  equivalent to declaring a reg as ``rand const``, but also works outside of
  checkers. (Yosys also supports ``rand const`` outside checkers.)

- The system function ``$anyseq`` evaluates to any value, possibly a different
  value in each cycle. This is equivalent to declaring a reg as ``rand``, but
  also works outside of checkers. (Yosys also supports ``rand`` variables
  outside checkers.)

- The system functions ``$allconst`` and ``$allseq`` can be used to construct
  formal exist-forall problems. Assumptions only hold if the trace satisfies the
  assumption for all ``$allconst/$allseq`` values. For assertions and cover
  statements it is sufficient if just one ``$allconst/$allseq`` value triggers
  the property (similar to ``$anyconst/$anyseq``).

- Wires/registers declared using the ``anyconst/anyseq/allconst/allseq``
  attribute (for example ``(* anyconst *) reg [7:0] foobar;``) will behave as if
  driven by a ``$anyconst/$anyseq/$allconst/$allseq`` function.

- The SystemVerilog tasks ``$past``, ``$stable``, ``$rose`` and ``$fell`` are
  supported in any clocked block.

- The syntax ``@($global_clock)`` can be used to create FFs that have no
  explicit clock input (``$ff`` cells). The same can be achieved by using
  ``@(posedge <netname>)`` or ``@(negedge <netname>)`` when ``<netname>`` is
  marked with the ``(* gclk *)`` Verilog attribute.


Supported features from SystemVerilog
-------------------------------------

When `read_verilog` is called with ``-sv``, it accepts some language features
from SystemVerilog:

- The ``assert`` statement from SystemVerilog is supported in its most basic
  form. In module context: ``assert property (<expression>);`` and within an
  always block: ``assert(<expression>);``. It is transformed to an ``$assert``
  cell.

- The ``assume``, ``restrict``, and ``cover`` statements from SystemVerilog are
  also supported. The same limitations as with the ``assert`` statement apply.

- The keywords ``always_comb``, ``always_ff`` and ``always_latch``, ``logic``
  and ``bit`` are supported.

- Declaring free variables with ``rand`` and ``rand const`` is supported.

- Checkers without a port list that do not need to be instantiated (but instead
  behave like a named block) are supported.

- SystemVerilog packages are supported. Once a SystemVerilog file is read into a
  design with `read_verilog`, all its packages are available to SystemVerilog
  files being read into the same design afterwards.

- typedefs are supported (including inside packages)
	- type casts are currently not supported

- enums are supported (including inside packages)
	- but are currently not strongly typed

- packed structs and unions are supported
	- arrays of packed structs/unions are currently not supported
	- structure literals are currently not supported

- multidimensional arrays are supported
	- array assignment of unpacked arrays is currently not supported
	- array literals are currently not supported

- SystemVerilog interfaces (SVIs) are supported. Modports for specifying whether
  ports are inputs or outputs are supported.

- Assignments within expressions are supported.

- The ``unique``, ``unique0``, and ``priority`` SystemVerilog keywords are
  accepted on ``if`` and ``case`` conditionals.  (Those keywords are currently
  handled in the same way as their equivalent ``full_case`` and
  ``parallel_case`` attributes on ``case`` statements, and checked
  for syntactic validity but otherwise ignored on ``if`` statements.)
