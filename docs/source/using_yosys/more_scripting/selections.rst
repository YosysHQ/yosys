Selections
----------

.. role:: yoscrypt(code)
   :language: yoscrypt

The selection framework
~~~~~~~~~~~~~~~~~~~~~~~

.. todo:: reduce overlap with :doc:`/getting_started/scripting_intro` select section

The :cmd:ref:`select` command can be used to create a selection for subsequent
commands. For example:

.. code:: yoscrypt

    select foobar         # select the module foobar
    delete                # delete selected objects

Normally the :cmd:ref:`select` command overwrites a previous selection. The
commands :yoscrypt:`select -add` and :yoscrypt:`select -del` can be used to add
or remove objects from the current selection.

The command :yoscrypt:`select -clear` can be used to reset the selection to the
default, which is a complete selection of everything in the current module.

This selection framework can also be used directly in many other commands.
Whenever a command has ``[selection]`` as last argument in its usage help, this
means that it will use the engine behind the :cmd:ref:`select` command to
evaluate additional arguments and use the resulting selection instead of the
selection created by the last :cmd:ref:`select` command.

For example, the command :cmd:ref:`delete` will delete everything in the current
selection; while :yoscrypt:`delete foobar` will only delete the module foobar.
If no :cmd:ref:`select` command has been made, then the "current selection" will
be the whole design.

.. note:: Many of the examples on this page make use of the :cmd:ref:`show` 
   command to visually demonstrate the effect of selections.  For a more 
   detailed look at this command, refer to :ref:`interactive_show`.

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

Commands can be executed in *module/* or *design/* context. Until now, all
commands have been executed in design context. The :cmd:ref:`cd` command can be
used to switch to module context.

In module context, all commands only effect the active module. Objects in the
module are selected without the ``<module_name>/`` prefix. For example:

.. code:: yoscrypt

    cd foo                # switch to module foo
    delete bar            # delete object foo/bar

    cd mycpu              # switch to module mycpu
    dump reg_*            # print details on all objects whose names start with reg_

    cd ..                 # switch back to design

Note: Most synthesis scripts never switch to module context. But it is a very
powerful tool which we explore more in
:doc:`/using_yosys/more_scripting/interactive_investigation`.

Selecting by object property or type
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Special patterns can be used to select by object property or type. For example:

- select all wires whose names start with ``reg_``: :yoscrypt:`select w:reg_*`
- select all objects with the attribute ``foobar`` set: :yoscrypt:`select
  a:foobar`
- select all objects with the attribute ``foobar`` set to 42: :yoscrypt:`select
  a:foobar=42`
- select all modules with the attribute ``blabla`` set: :yoscrypt:`select
  A:blabla`
- select all $add cells from the module foo: :yoscrypt:`select foo/t:$add`

A complete list of pattern expressions can be found in :doc:`/cmd/select`.

Operations on selections
~~~~~~~~~~~~~~~~~~~~~~~~

Combining selections
^^^^^^^^^^^^^^^^^^^^

The :cmd:ref:`select` command is actually much more powerful than it might seem
at first glance. When it is called with multiple arguments, each argument is
evaluated and pushed separately on a stack. After all arguments have been
processed it simply creates the union of all elements on the stack. So
:yoscrypt:`select t:$add a:foo` will select all ``$add`` cells and all objects
with the ``foo`` attribute set:   

.. literalinclude:: /code_examples/selections/foobaraddsub.v
   :caption: Test module for operations on selections
   :name: foobaraddsub
   :language: verilog

.. code-block::
   :caption: Output for command ``select t:$add a:foo -list`` on :numref:`foobaraddsub`

   yosys> select t:$add a:foo -list
   foobaraddsub/$add$foobaraddsub.v:6$3
   foobaraddsub/$sub$foobaraddsub.v:5$2
   foobaraddsub/$add$foobaraddsub.v:4$1

In many cases simply adding more and more stuff to the selection is an
ineffective way of selecting the interesting part of the design. Special
arguments can be used to combine the elements on the stack. For example the
``%i`` arguments pops the last two elements from the stack, intersects them, and
pushes the result back on the stack. So :yoscrypt:`select t:$add a:foo %i` will
select all ``$add`` cells that have the ``foo`` attribute set:

.. code-block::
   :caption: Output for command ``select t:$add a:foo %i -list`` on :numref:`foobaraddsub`
   
   yosys> select t:$add a:foo %i -list
   foobaraddsub/$add$foobaraddsub.v:4$1

Some of the special ``%``-codes:

- ``%u``: union of top two elements on stack -- pop 2, push 1
- ``%d``: difference of top two elements on stack -- pop 2, push 1
- ``%i``: intersection of top two elements on stack -- pop 2, push 1
- ``%n``: inverse of top element on stack -- pop 1, push 1

See :doc:`/cmd/select` for the full list.

Expanding selections
^^^^^^^^^^^^^^^^^^^^

:numref:`sumprod` uses the Yosys non-standard ``{... *}`` syntax to set the
attribute ``sumstuff`` on all cells generated by the first assign statement.
(This works on arbitrary large blocks of Verilog code and can be used to mark
portions of code for analysis.)

.. literalinclude:: /code_examples/selections/sumprod.v
   :caption: Another test module for operations on selections
   :name: sumprod
   :language: verilog

Selecting ``a:sumstuff`` in this module will yield the following circuit
diagram:

.. figure:: /_images/code_examples/selections/sumprod_00.*
   :class: width-helper invert-helper
   :name: sumprod_00

   Output of ``show a:sumstuff`` on :numref:`sumprod`

As only the cells themselves are selected, but not the temporary wire ``$1_Y``,
the two adders are shown as two disjunct parts. This can be very useful for
global signals like clock and reset signals: just unselect them using a command
such as :yoscrypt:`select -del clk rst` and each cell using them will get its
own net label.

In this case however we would like to see the cells connected properly. This can
be achieved using the ``%x`` action, that broadens the selection, i.e. for each
selected wire it selects all cells connected to the wire and vice versa. So
:yoscrypt:`show a:sumstuff %x` yields the diagram shown in :numref:`sumprod_01`:

.. figure:: /_images/code_examples/selections/sumprod_01.*
   :class: width-helper invert-helper
   :name: sumprod_01

   Output of ``show a:sumstuff %x`` on :numref:`sumprod`

.. _selecting_logic_cones:

Selecting logic cones
^^^^^^^^^^^^^^^^^^^^^

:numref:`sumprod_01` shows what is called the ``input cone`` of ``sum``, i.e.
all cells and signals that are used to generate the signal ``sum``. The ``%ci``
action can be used to select the input cones of all object in the top selection
in the stack maintained by the :cmd:ref:`select` command.

As with the ``%x`` action, these commands broaden the selection by one "step".
But this time the operation only works against the direction of data flow. That
means, wires only select cells via output ports and cells only select wires via
input ports.

The following sequence of diagrams demonstrates this step-wise expansion:

.. figure:: /_images/code_examples/selections/sumprod_02.*
   :class: width-helper invert-helper

   Output of :yoscrypt:`show prod` on :numref:`sumprod`

.. figure:: /_images/code_examples/selections/sumprod_03.*
   :class: width-helper invert-helper

   Output of :yoscrypt:`show prod %ci` on :numref:`sumprod`

.. figure:: /_images/code_examples/selections/sumprod_04.*
   :class: width-helper invert-helper

   Output of :yoscrypt:`show prod %ci %ci` on :numref:`sumprod`

.. figure:: /_images/code_examples/selections/sumprod_05.*
   :class: width-helper invert-helper

   Output of :yoscrypt:`show prod %ci %ci %ci` on :numref:`sumprod`

Notice the subtle difference between :yoscrypt:`show prod %ci` and
:yoscrypt:`show prod %ci %ci`.  Both images show the ``$mul`` cell driven by
some inputs ``$3_Y`` and ``c``.  However it is not until the second image,
having called ``%ci`` the second time, that :cmd:ref:`show` is able to
distinguish between ``$3_Y`` being a wire and ``c`` being an input.  We can see
this better with the :cmd:ref:`dump` command instead:

.. literalinclude:: /code_examples/selections/sumprod.out
   :language: RTLIL
   :end-at: end
   :caption: Output of :yoscrypt:`dump prod %ci`

.. literalinclude:: /code_examples/selections/sumprod.out
   :language: RTLIL
   :start-after: end
   :caption: Output of :yoscrypt:`dump prod %ci %ci`

When selecting many levels of logic, repeating ``%ci`` over and over again can
be a bit dull. So there is a shortcut for that: the number of iterations can be
appended to the action. So for example the action ``%ci3`` is identical to
performing the ``%ci`` action three times.

The action ``%ci*`` performs the ``%ci`` action over and over again until it
has no effect anymore.

.. _advanced_logic_cones:

Advanced logic cone selection
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

In most cases there are certain cell types and/or ports that should not be
considered for the ``%ci`` action, or we only want to follow certain cell types
and/or ports. This can be achieved using additional patterns that can be
appended to the ``%ci`` action.

Lets consider :numref:`memdemo_src`. It serves no purpose other than being a
non-trivial circuit for demonstrating some of the advanced Yosys features. This
code is available in ``docs/source/code_examples/selections`` of the Yosys
source repository.

.. literalinclude:: /code_examples/selections/memdemo.v
   :caption: :file:`memdemo.v`
   :name: memdemo_src
   :language: verilog

The script :file:`memdemo.ys` is used to generate the images included here. Let's
look at the first section:

.. literalinclude:: /code_examples/selections/memdemo.ys
   :caption: Synthesizing :ref:`memdemo_src`
   :name: memdemo_ys
   :language: yoscrypt
   :end-at: opt

This loads :numref:`memdemo_src` and synthesizes the included module. Note that
this code can be copied and run directly in a Yosys command line session,
provided :file:`memdemo.v` is in the same directory. We can now change to the
``memdemo`` module with ``cd memdemo``, and call :cmd:ref:`show` to see the
diagram in :numref:`memdemo_00`.

.. figure:: /_images/code_examples/selections/memdemo_00.*
   :class: width-helper invert-helper
   :name: memdemo_00
   
   Complete circuit diagram for the design shown in :numref:`memdemo_src`

There's a lot going on there, but maybe we are only interested in the tree of
multiplexers that select the output value. Let's start by just showing the
output signal, ``y``, and its immediate predecessors. Remember `Selecting logic
cones`_ from above, we can use :yoscrypt:`show y %ci2`:

.. figure:: /_images/code_examples/selections/memdemo_01.*
   :class: width-helper invert-helper
   :name: memdemo_01
   
   Output of :yoscrypt:`show y %ci2`

From this we would learn that ``y`` is driven by a ``$dff cell``, that ``y`` is
connected to the output port ``Q``, that the ``clk`` signal goes into the
``CLK`` input port of the cell, and that the data comes from an auto-generated
wire into the input ``D`` of the flip-flop cell (indicated by the ``$`` at the
start of the name).  Let's go a bit further now and try :yoscrypt:`show y %ci5`:

.. figure:: /_images/code_examples/selections/memdemo_02.*
   :class: width-helper invert-helper
   :name: memdemo_02
   
   Output of :yoscrypt:`show y %ci5`

That's starting to get a bit messy, so maybe we want to ignore the mux select
inputs. To add a pattern we add a colon followed by the pattern to the ``%ci``
action. The pattern itself starts with ``-`` or ``+``, indicating if it is an
include or exclude pattern, followed by an optional comma separated list of cell
types, followed by an optional comma separated list of port names in square
brackets.  In this case, we want to exclude the ``S`` port of the ``$mux`` cell
type with :yoscrypt:`show y %ci5:-$mux[S]`:

.. figure:: /_images/code_examples/selections/memdemo_03.*
   :class: width-helper invert-helper
   :name: memdemo_03
   
   Output of :yoscrypt:`show y %ci5:-$mux[S]`

We could use a command such as :yoscrypt:`show y %ci2:+$dff[Q,D]
%ci*:-$mux[S]:-$dff` in which the first ``%ci`` jumps over the initial d-type
flip-flop and the 2nd action selects the entire input cone without going over
multiplexer select inputs and flip-flop cells:

.. figure:: /_images/code_examples/selections/memdemo_05.*
   :class: width-helper invert-helper
   :name: memdemo_05
   
   Output of ``show y %ci2:+$dff[Q,D] %ci*:-$mux[S]:-$dff``

Or we could use :yoscrypt:`show y %ci*:-[CLK,S]:+$dff:+$mux` instead, following
the input cone all the way but only following ``$dff`` and ``$mux`` cells, and
ignoring any ports named ``CLK`` or ``S``:

.. TODO:: pending discussion on whether rule ordering is a bug or a feature

.. figure:: /_images/code_examples/selections/memdemo_04.*
   :class: width-helper invert-helper
   :name: memdemo_04
   
   Output of :yoscrypt:`show y %ci*:-[CLK,S]:+$dff,$mux`

Similar to ``%ci`` exists an action ``%co`` to select output cones that accepts
the same syntax for pattern and repetition. The ``%x`` action mentioned
previously also accepts this advanced syntax.

These actions for traversing the circuit graph, combined with the actions for
boolean operations such as intersection (``%i``) and difference (``%d``) are
powerful tools for extracting the relevant portions of the circuit under
investigation.

Again, see :doc:`/cmd/select` for full documentation of these expressions.

Incremental selection
^^^^^^^^^^^^^^^^^^^^^

Sometimes a selection can most easily be described by a series of add/delete
operations. As mentioned previously, the commands :yoscrypt:`select -add` and
:yoscrypt:`select -del` respectively add or remove objects from the current
selection instead of overwriting it.

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

Storing and recalling selections
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. todo:: reflow for not presentation

The current selection can be stored in memory with the command ``select -set
<name>``. It can later be recalled using ``select @<name>``. In fact, the
``@<name>`` expression pushes the stored selection on the stack maintained by
the :cmd:ref:`select` command. So for example :yoscrypt:`select @foo @bar %i`
will select the intersection between the stored selections ``foo`` and ``bar``.

In larger investigation efforts it is highly recommended to maintain a script
that sets up relevant selections, so they can easily be recalled, for example
when Yosys needs to be re-run after a design or source code change.

The :cmd:ref:`history` command can be used to list all recent interactive
commands. This feature can be useful for creating such a script from the
commands used in an interactive session.

Remember that select expressions can also be used directly as arguments to most
commands. Some commands also accept a single select argument to some options. In
those cases selection variables must be used to capture more complex selections.

Example code from |code_examples/selections|_:

.. |code_examples/selections| replace:: :file:`docs/source/code_examples/selections`
.. _code_examples/selections: https://github.com/YosysHQ/yosys/tree/main/docs/source/code_examples/selections

.. literalinclude:: /code_examples/selections/select.v
   :language: verilog
   :caption: :file:`select.v`

.. literalinclude:: /code_examples/selections/select.ys
   :language: yoscrypt
   :caption: :file:`select.ys`
   :name: select_ys

.. figure:: /_images/code_examples/selections/select.*
    :class: width-helper invert-helper

    Circuit diagram produced by :numref:`select_ys`
