Selections
----------

.. todo:: expand on text

Most Yosys commands make use of the "selection framework" of Yosys. It can be
used to apply commands only to part of the design. For example:

.. code:: yoscrypt

    delete                # will delete the whole design, but

    delete foobar         # will only delete the module foobar.

The :cmd:ref:`select` command can be used to create a selection for subsequent
commands. For example:

.. code:: yoscrypt

    select foobar         # select the module foobar
    delete                # delete selected objects
    select -clear         # reset selection (select whole design)

See :doc:`/cmd/select`

How to make a selection
~~~~~~~~~~~~~~~~~~~~~~~

Selection by object name
^^^^^^^^^^^^^^^^^^^^^^^^

The easiest way to select objects is by object name. This is usually only done
in synthesis scripts that are hand-tailored for a specific design.

.. code:: yoscrypt

    select foobar         # select module foobar
    select foo*           # select all modules whose names start with foo
    select foo*/bar*      # select all objects matching bar* from modules matching foo*
    select */clk          # select objects named clk from all modules

Module and design context
^^^^^^^^^^^^^^^^^^^^^^^^^

Commands can be executed in *module/* or *design/* context. Until now all
commands have been executed in design context. The :cmd:ref:`cd` command can be
used to switch to module context.

In module context all commands only effect the active module. Objects in the
module are selected without the ``<module_name>/`` prefix. For example:

.. code:: yoscrypt

    cd foo                # switch to module foo
    delete bar            # delete object foo/bar

    cd mycpu              # switch to module mycpu
    dump reg_*            # print details on all objects whose names start with reg_

    cd ..                 # switch back to design

Note: Most synthesis scripts never switch to module context. But it is a very
powerful tool for interactive design investigation.

Selecting by object property or type
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Special patterns can be used to select by object property or type. For example:

.. code:: yoscrypt

    select w:reg_*        # select all wires whose names start with reg_
    select a:foobar       # select all objects with the attribute foobar set
    select a:foobar=42    # select all objects with the attribute foobar set to 42
    select A:blabla       # select all modules with the attribute blabla set
    select foo/t:$add     # select all $add cells from the module foo

A complete list of this pattern expressions can be found in the command
reference to the :cmd:ref:`select` command.

Combining selection
^^^^^^^^^^^^^^^^^^^

When more than one selection expression is used in one statement, then they are
pushed on a stack. The final elements on the stack are combined into a union:

.. code:: yoscrypt

    select t:$dff r:WIDTH>1     # all cells of type $dff and/or with a parameter WIDTH > 1

Special ``%``-commands can be used to combine the elements on the stack:

.. code:: yoscrypt

    select t:$dff r:WIDTH>1 %i  # all cells of type $dff *AND* with a parameter WIDTH > 1

Examples for ``%``-codes (see :doc:`/cmd/select` for full list):

- ``%u``: union of top two elements on stack -- pop 2, push 1
- ``%d``: difference of top two elements on stack -- pop 2, push 1
- ``%i``: intersection of top two elements on stack -- pop 2, push 1
- ``%n``: inverse of top element on stack -- pop 1, push 1

Expanding selections
^^^^^^^^^^^^^^^^^^^^

Selections of cells and wires can be expanded along connections using
``%``-codes for selecting input cones (``%ci``), output cones (``%co``), or
both (``%x``).

.. code:: yoscrypt

    # select all wires that are inputs to $add cells
    select t:$add %ci w:* %i

Additional constraints such as port names can be specified.

.. code:: yoscrypt

    # select all wires that connect a "Q" output with a "D" input
    select c:* %co:+[Q] w:* %i c:* %ci:+[D] w:* %i %i

    # select the multiplexer tree that drives the signal 'state'
    select state %ci*:+$mux,$pmux[A,B,Y]

See :doc:`/cmd/select` for full documentation of these expressions.

Incremental selection
^^^^^^^^^^^^^^^^^^^^^

Sometimes a selection can most easily be described by a series of add/delete
operations. The commands ``select -add`` and ``select -del`` respectively add or
remove objects from the current selection instead of overwriting it.

.. code:: yoscrypt

    select -none            # start with an empty selection
    select -add reg_*       # select a bunch of objects
    select -del reg_42      # but not this one
    select -add state %ci   # and add more stuff

Within a select expression the token ``%`` can be used to push the previous selection
on the stack.

.. code:: yoscrypt

    select t:$add t:$sub    # select all $add and $sub cells
    select % %ci % %d       # select only the input wires to those cells

Creating selection variables
^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Selections can be stored under a name with the ``select -set <name>``
command. The stored selections can be used in later select expressions
using the syntax ``@<name>``.

.. code:: yoscrypt

    select -set cone_a state_a %ci*:-$dff  # set @cone_a to the input cone of state_a
    select -set cone_b state_b %ci*:-$dff  # set @cone_b to the input cone of state_b
    select @cone_a @cone_b %i              # select the objects that are in both cones

Remember that select expressions can also be used directly as arguments to most
commands. Some commands also except a single select argument to some options.
In those cases selection variables must be used to capture more complex selections.

.. code:: yoscrypt

    dump @cone_a @cone_b

    select -set cone_ab @cone_a @cone_b %i
    show -color red @cone_ab -color magenta @cone_a -color blue @cone_b

Example:

.. literalinclude:: ../../../resources/PRESENTATION_ExAdv/select.v
   :language: verilog
   :caption: ``docs/resources/PRESENTATION_ExAdv/select.v``

.. literalinclude:: ../../../resources/PRESENTATION_ExAdv/select.ys
   :language: yoscrypt
   :caption: ``docs/resources/PRESENTATION_ExAdv/select.ys``

.. figure:: ../../../images/res/PRESENTATION_ExAdv/select.*
    :class: width-helper

Interactive Design Investigation
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Yosys can also be used to investigate designs (or netlists created from other
tools).

- The selection mechanism, especially patterns such as ``%ci`` and ``%co``, can
  be used to figure out how parts of the design are connected.
- Commands such as :cmd:ref:`submod`, :cmd:ref:`expose`, and :cmd:ref:`splice`
  can be used to transform the design into an equivalent design that is easier
  to analyse.
- Commands such as :cmd:ref:`eval` and :cmd:ref:`sat` can be used to investigate
  the behavior of the circuit.
- :doc:`/cmd/show`.
- :doc:`/cmd/dump`.
- :doc:`/cmd/add` and :doc:`/cmd/delete` can be used to modify and reorganize a
  design dynamically.

Changing design hierarchy
^^^^^^^^^^^^^^^^^^^^^^^^^

Commands such as :cmd:ref:`flatten` and :cmd:ref:`submod` can be used to change
the design hierarchy, i.e. flatten the hierarchy or moving parts of a module to
a submodule. This has applications in synthesis scripts as well as in reverse
engineering and analysis.  An example using :cmd:ref:`submod` is shown below for
reorganizing a module in Yosys and checking the resulting circuit.

.. literalinclude:: ../../../resources/PRESENTATION_ExOth/scrambler.v
   :language: verilog
   :caption: ``docs/resources/PRESENTATION_ExOth/scrambler.v``

.. code:: yoscrypt

    read_verilog scrambler.v

    hierarchy; proc;;

    cd scrambler
    submod -name xorshift32 \
            xs %c %ci %D %c %ci:+[D] %D \
            %ci*:-$dff xs %co %ci %d

.. figure:: ../../../images/res/PRESENTATION_ExOth/scrambler_p01.*
    :class: width-helper

.. figure:: ../../../images/res/PRESENTATION_ExOth/scrambler_p02.*
    :class: width-helper

Analyzing the resulting circuit with :doc:`/cmd/eval`:

.. code:: text

    > cd xorshift32
    > rename n2 in
    > rename n1 out

    > eval -set in 1 -show out
    Eval result: \out = 270369.

    > eval -set in 270369 -show out
    Eval result: \out = 67634689.

    > sat -set out 632435482
    Signal Name                 Dec        Hex                                   Bin
    -------------------- ---------- ---------- -------------------------------------
    \in                   745495504   2c6f5bd0      00101100011011110101101111010000
    \out                  632435482   25b2331a      00100101101100100011001100011010

Behavioral changes
^^^^^^^^^^^^^^^^^^

Commands such as :cmd:ref:`techmap` can be used to make behavioral changes to
the design, for example changing asynchronous resets to synchronous resets. This
has applications in design space exploration (evaluation of various
architectures for one circuit).

The following techmap map file replaces all positive-edge async reset flip-flops
with positive-edge sync reset flip-flops. The code is taken from the example
Yosys script for ASIC synthesis of the Amber ARMv2 CPU.

.. code:: verilog

    (* techmap_celltype = "$adff" *)
    module adff2dff (CLK, ARST, D, Q);

        parameter WIDTH = 1;
        parameter CLK_POLARITY = 1;
        parameter ARST_POLARITY = 1;
        parameter ARST_VALUE = 0;

        input CLK, ARST;
        input [WIDTH-1:0] D;
        output reg [WIDTH-1:0] Q;

        wire [1023:0] _TECHMAP_DO_ = "proc";

        wire _TECHMAP_FAIL_ = !CLK_POLARITY || !ARST_POLARITY;

        always @(posedge CLK)
            if (ARST)
                Q <= ARST_VALUE;
            else
                <= D;

    endmodule

For more on the :cmd:ref:`techmap` command, see the page on
:doc:`/yosys_internals/techmap`.
