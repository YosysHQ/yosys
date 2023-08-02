Scripting in Yosys
------------------

.. TODO: copypaste

Yosys reads and processes commands from synthesis scripts, command line
arguments and an interactive command prompt. Yosys commands consist of a command
name and an optional whitespace separated list of arguments. Commands are
terminated using the newline character or a semicolon (;). Empty lines and lines
starting with the hash sign (#) are ignored. See :ref:`sec:typusecase` for an
example synthesis script.

The command ``help`` can be used to access the command reference manual.

Most commands can operate not only on the entire design but also specifically on
selected parts of the design. For example the command dump will print all
selected objects in the current design while dump foobar will only print the
module foobar and dump \* will print the entire design regardless of the current
selection.

.. code:: yoscrypt

	dump */t:$add %x:+[A] \*/w:\* %i

The selection mechanism is very powerful. For example the command above will
print all wires that are connected to the ``\A`` port of a ``$add`` cell.
Detailed documentation of the select framework can be found in the command
reference for the ``select`` command.
