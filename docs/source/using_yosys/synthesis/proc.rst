Converting process blocks
~~~~~~~~~~~~~~~~~~~~~~~~~

.. role:: yoscrypt(code)
   :language: yoscrypt

The Verilog frontend converts ``always``-blocks to RTL netlists for the
expressions and "processess" for the control- and memory elements. The
:cmd:ref:`proc` command then transforms these "processess" to netlists of RTL
multiplexer and register cells. It also is a macro command that calls the other
``proc_*`` commands in a sensible order:

.. literalinclude:: /code_examples/macro_commands/proc.ys
   :language: yoscrypt
   :start-after: #end:
   :caption: Passes called by :cmd:ref:`proc`

After all the ``proc_*`` commands, :cmd:ref:`opt_expr` is called. This can be
disabled by calling :yoscrypt:`proc -noopt`.  For more information about
:cmd:ref:`proc`, such as disabling certain sub commands, see :doc:`/cmd/proc`.

Many commands can not operate on modules with "processess" in them. Usually a
call to :cmd:ref:`proc` is the first command in the actual synthesis procedure
after design elaboration.

Example
^^^^^^^

.. todo:: describe ``proc`` images

|code_examples/synth_flow|_.

.. |code_examples/synth_flow| replace:: :file:`docs/source/code_examples/synth_flow`
.. _code_examples/synth_flow: https://github.com/YosysHQ/yosys/tree/main/docs/source/code_examples/synth_flow

.. literalinclude:: /code_examples/synth_flow/proc_01.v
   :language: verilog
   :caption: :file:`proc_01.v`

.. literalinclude:: /code_examples/synth_flow/proc_01.ys
   :language: yoscrypt
   :caption: :file:`proc_01.ys`

.. figure:: /_images/code_examples/synth_flow/proc_01.*
   :class: width-helper invert-helper

.. figure:: /_images/code_examples/synth_flow/proc_02.*
   :class: width-helper invert-helper

.. literalinclude:: /code_examples/synth_flow/proc_02.v
   :language: verilog
   :caption: :file:`proc_02.v`

.. literalinclude:: /code_examples/synth_flow/proc_02.ys
   :language: yoscrypt
   :caption: :file:`proc_02.ys`

.. figure:: /_images/code_examples/synth_flow/proc_03.*
   :class: width-helper invert-helper

.. literalinclude:: /code_examples/synth_flow/proc_03.ys
   :language: yoscrypt
   :caption: :file:`proc_03.ys`

.. literalinclude:: /code_examples/synth_flow/proc_03.v
   :language: verilog
   :caption: :file:`proc_03.v`
