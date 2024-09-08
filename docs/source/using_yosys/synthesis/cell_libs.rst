Mapping to cell libraries
-------------------------

.. role:: yoscrypt(code)
   :language: yoscrypt

While much of this documentation focuses on the use of Yosys with FPGAs, it is
also possible to map to cell libraries which can be used in designing ASICs.
This section will cover a brief `example project`_, available in the Yosys
source code under :file:`docs/source/code_examples/intro/`.  The project
contains a simple ASIC synthesis script (:file:`counter.ys`), a digital design
written in Verilog (:file:`counter.v`), and a simple CMOS cell library
(:file:`mycells.lib`).  Many of the early steps here are already covered in more
detail in the :doc:`/getting_started/example_synth` document.

.. note::

   The :file:`counter.ys` script includes the commands used to generate the
   images in this document.  Code snippets in this document skip these commands;
   including line numbers to allow the reader to follow along with the source.
   
   To learn more about these commands, check out :ref:`interactive_show`.

.. _example project: https://github.com/YosysHQ/yosys/tree/main/docs/source/code_examples/intro

A simple counter
~~~~~~~~~~~~~~~~

First, let's quickly look at the design:

.. literalinclude:: /code_examples/intro/counter.v
   :language: Verilog
   :linenos:
   :name: counter-v
   :caption: :file:`counter.v`

This is a simple counter with reset and enable.  If the reset signal, ``rst``,
is high then the counter will reset to 0.  Otherwise, if the enable signal,
``en``, is high then the ``count`` register will increment by 1 each rising edge
of the clock, ``clk``.  

Loading the design
~~~~~~~~~~~~~~~~~~

.. literalinclude:: /code_examples/intro/counter.ys
   :language: yoscrypt
   :lines: 1-3
   :lineno-match:
   :caption: :file:`counter.ys` - read design

Our circuit now looks like this:

.. figure:: /_images/code_examples/intro/counter_00.*
   :class: width-helper invert-helper
   :name: counter-hierarchy

   ``counter`` after :cmd:ref:`hierarchy`

Coarse-grain representation
~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. literalinclude:: /code_examples/intro/counter.ys
   :language: yoscrypt
   :lines: 7-10
   :lineno-match:
   :caption: :file:`counter.ys` - the high-level stuff

.. figure:: /_images/code_examples/intro/counter_01.*
   :class: width-helper invert-helper

   Coarse-grain representation of the ``counter`` module

Logic gate mapping
~~~~~~~~~~~~~~~~~~

.. literalinclude:: /code_examples/intro/counter.ys
   :language: yoscrypt
   :lines: 14-15
   :lineno-match:
   :caption: :file:`counter.ys` - mapping to internal cell library

.. figure:: /_images/code_examples/intro/counter_02.*
   :class: width-helper invert-helper

   ``counter`` after :cmd:ref:`techmap`

Mapping to hardware
~~~~~~~~~~~~~~~~~~~

For this example, we are using a Liberty file to describe a cell library which
our internal cell library will be mapped to:

.. todo:: find a Liberty pygments style?

.. literalinclude:: /code_examples/intro/mycells.lib
   :language: text
   :linenos:
   :name: mycells-lib
   :caption: :file:`mycells.lib`

Recall that the Yosys built-in logic gate types are ``$_NOT_``, ``$_AND_``,
``$_OR_``, ``$_XOR_``, and ``$_MUX_`` with an assortment of dff memory types.
:ref:`mycells-lib` defines our target cells as ``BUF``, ``NOT``, ``NAND``,
``NOR``, and ``DFF``.  Mapping between these is performed with the commands
:cmd:ref:`dfflibmap` and :cmd:ref:`abc` as follows:

.. literalinclude:: /code_examples/intro/counter.ys
   :language: yoscrypt
   :lines: 20-27
   :lineno-match:
   :caption: :file:`counter.ys` - mapping to hardware

The final version of our ``counter`` module looks like this:

.. figure:: /_images/code_examples/intro/counter_03.*
   :class: width-helper invert-helper

   ``counter`` after hardware cell mapping

Before finally being output as a verilog file with :cmd:ref:`write_verilog`,
which can then be loaded into another tool:

.. literalinclude:: /code_examples/intro/counter.ys
   :language: yoscrypt
   :lines: 30-31
   :lineno-match:
   :caption: :file:`counter.ys` - write synthesized design
