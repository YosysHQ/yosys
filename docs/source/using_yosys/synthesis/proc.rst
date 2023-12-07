Converting process blocks
~~~~~~~~~~~~~~~~~~~~~~~~~

The Verilog frontend converts ``always``-blocks to RTL netlists for the
expressions and "processess" for the control- and memory elements. The
:cmd:ref:`proc` command then transforms these "processess" to netlists of RTL
multiplexer and register cells. It also is a macro command that calls the other
``proc_*`` commands in a sensible order:

#. :cmd:ref:`proc_clean` removes empty branches and processes.
#. :cmd:ref:`proc_rmdead` removes unreachable branches.
#. :cmd:ref:`proc_prune`
#. :cmd:ref:`proc_init` special handling of "initial" blocks.
#. :cmd:ref:`proc_arst` identifies modeling of async resets.
#. :cmd:ref:`proc_rom`
#. :cmd:ref:`proc_mux` converts decision trees to multiplexer networks.
#. :cmd:ref:`proc_dlatch`
#. :cmd:ref:`proc_dff` extracts registers from processes.
#. :cmd:ref:`proc_memwr`
#. :cmd:ref:`proc_clean` this should remove all the processes, provided all went
   fine.

After all the ``proc_*`` commands, :yoscrypt:`opt_expr` is called. This can be
disabled by calling :yoscrypt:`proc -noopt`.  For more information about
:cmd:ref:`proc`, such as disabling certain sub commands, see :doc:`/cmd/proc`.

Many commands can not operate on modules with "processess" in them. Usually a
call to :cmd:ref:`proc` is the first command in the actual synthesis procedure
after design elaboration.

Example
^^^^^^^

.. todo:: describe ``proc`` images

.. literalinclude:: /code_examples/synth_flow/proc_01.v
   :language: verilog
   :caption: ``docs/source/code_examples/synth_flow/proc_01.v``

.. literalinclude:: /code_examples/synth_flow/proc_01.ys
   :language: yoscrypt
   :caption: ``docs/source/code_examples/synth_flow/proc_01.ys``

.. figure:: /_images/code_examples/synth_flow/proc_01.*
   :class: width-helper

.. figure:: /_images/code_examples/synth_flow/proc_02.*
   :class: width-helper

.. literalinclude:: /code_examples/synth_flow/proc_02.v
   :language: verilog
   :caption: ``docs/source/code_examples/synth_flow/proc_02.v``

.. literalinclude:: /code_examples/synth_flow/proc_02.ys
   :language: yoscrypt
   :caption: ``docs/source/code_examples/synth_flow/proc_02.ys``

.. figure:: /_images/code_examples/synth_flow/proc_03.*
   :class: width-helper

.. literalinclude:: /code_examples/synth_flow/proc_03.ys
   :language: yoscrypt
   :caption: ``docs/source/code_examples/synth_flow/proc_03.ys``

.. literalinclude:: /code_examples/synth_flow/proc_03.v
   :language: verilog
   :caption: ``docs/source/code_examples/synth_flow/proc_03.v``
