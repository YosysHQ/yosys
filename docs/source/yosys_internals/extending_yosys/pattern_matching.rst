Writing pattern matchers
========================

The header ``kernel/matcher.h`` is a small C++ library for writing pattern
matchers.

The "patterns" in this context are subgraphs in a Yosys RTLIL netlist.

The algorithm used in a pattern matcher is a simple recursive search with
backtracking. It is left to the author of the matcher to determine an efficient
cell order for the search that allows for maximum use of indices and early
backtracking.

The examples on this page are taken from
:file:`tests/unit/kernel/matcherDocTest.cc`, where they are compiled and tested.

API of a matcher
----------------

A pattern is a struct derived from ``MatchPattern<Pattern, Match>``, where
``Match`` is a struct holding the state variables of the pattern. It is
instantiated with a ``MatchContext`` for an RTLIL module and a list of cells
from that module:

.. literalinclude:: ../../../../tests/unit/kernel/matcherDocTest.cc
   :language: cpp
   :tab-width: 4
   :start-after: [setup]
   :end-before: [/setup]
   :dedent:

The caller must make sure that none of the cells in the 2nd argument are
deleted for as long as the pattern matcher instance is used.

At any time it is possible to disable cells, preventing them from showing up in
any future matches:

.. literalinclude:: ../../../../tests/unit/kernel/matcherDocTest.cc
   :language: cpp
   :tab-width: 4
   :start-after: [blacklist]
   :end-before: [/blacklist]
   :dedent:

The ``run(callback_function)`` method searches for all matches for the pattern
and calls the callback function for each found match:

.. literalinclude:: ../../../../tests/unit/kernel/matcherDocTest.cc
   :language: cpp
   :tab-width: 4
   :start-after: [foobar_callback]
   :end-before: [/foobar_callback]

.. literalinclude:: ../../../../tests/unit/kernel/matcherDocTest.cc
   :language: cpp
   :tab-width: 4
   :start-after: [run]
   :end-before: [/run]
   :dedent:

The state variables of the pattern are the members of its ``Match`` struct,
which is passed to the callback.

User data variables are plain members of the pattern struct.

The callback is optional. ``run()`` returns the number of found matches.

Declaring a pattern
-------------------

The constructor of a pattern passes the first stage of the search to
``MatchPattern`` and builds the indices of the pattern from the cell list. The
stages follow as further member functions:

.. literalinclude:: ../../../../tests/unit/kernel/matcherDocTest.cc
   :language: cpp
   :tab-width: 4
   :start-at: struct Foobar :
   :end-before: [/foobar_decl]

Declaring state variables
-------------------------

State variables are declared as members of the ``Match`` struct. For example:

.. literalinclude:: ../../../../tests/unit/kernel/matcherDocTest.cc
   :language: cpp
   :tab-width: 4
   :start-after: [foobar_match]
   :end-before: [/foobar_match]

Every stage of the search receives the ``Match`` by const reference and copies
it before modifying it, so state variables are saved and restored as needed by
the backtracking.

They are automatically initialized to the default constructed value of their type
when ``run()`` is called.

Declaring udata variables
-------------------------

Udata (user-data) variables can be used for example to configure the matcher or
the callback function used to perform actions on found matches.

There is no automatic management of udata variables. For this reason it is
recommended that the user-supplied matcher code treats them as read-only
variables.

They are declared as members of the pattern struct:

.. literalinclude:: ../../../../tests/unit/kernel/matcherDocTest.cc
   :language: cpp
   :tab-width: 4
   :start-after: [udata]
   :end-before: [/udata]
   :dedent:

They are initialized when the pattern matcher object is constructed.

Helper functions
----------------

``MatchPatternBase`` provides some functions that make it a bit easier to write
matchers:

- The ``port(<cell>, <portname>)`` function is a handy alias for
  ``sigmap(<cell>->getPort(<portname>))``.

- Similarly ``param(<cell>, <paramname>)`` looks up a parameter on a cell.

- The function ``nusers(<sigspec>)`` returns the number of different cells
  connected to any of the given signal bits, plus one if any of the signal
  bits is also a primary input or primary output.

- ``add_siguser(<sigspec>, <cell>)`` records ``<cell>`` as a user of the given
  signal bits, so that ``nusers`` accounts for connections made while matching.

- ``blacklisted(<cell>)`` returns ``true`` if the cell has been blacklisted.

- ``autoremove(<cell>)`` blacklists the cell and removes it from the module
  when the ``MatchContext`` is destroyed.

Matching cells
--------------

Cells are matched by match stages, one member function per matched cell. For
example, the candidates for ``mul`` are selected and indexed in the constructor:

.. literalinclude:: ../../../../tests/unit/kernel/matcherDocTest.cc
   :language: cpp
   :tab-width: 4
   :start-at: if (cell->type == ID($mul)
   :end-at: mul_index.add(
   :dedent:

and matched by the stage:

.. literalinclude:: ../../../../tests/unit/kernel/matcherDocTest.cc
   :language: cpp
   :tab-width: 4
   :start-after: [match_mul]
   :end-before: [/match_mul]
   :dedent:

A match stage stores the matched cell in a state variable of type ``Cell*``, here
``mul``, and calls the next stage, here ``code_width``, for each candidate.
``candidates()`` skips blacklisted cells. ``descend()`` calls the next stage
inside the ``MatchFrame`` and returns ``true`` when a matched cell got
blacklisted, which ends the loop early.

A match stage without conditions in the loop, without a guard and without the
call after the loop is a single ``match_each()`` call, for example
``match_each(m, ff_cells, &Match::ff, &Foobar::match_mul)``.

The guard ``if (m.ff)`` makes the match conditional. If it evaluates to
``false`` then the match is skipped and the corresponding state variable is set
to ``nullptr``. In our example we only try to match the ``mul`` cell if the
``ff`` state variable points to a cell. (``ff`` is provided by the prior match
stage ``match_ff``.)

The conditions in the constructor are evaluated once for each cell when the
matcher is constructed. A match stage will only consider cells for which these
conditions evaluated to ``true``. Note that the cell being added is the only
state these conditions may use.

The key of an index is computed from the cell when the matcher is constructed.
The key it is looked up with is computed when the match is calculated, as a
function of any state variables assigned to by previous stages. Only cells whose
keys compare equal are considered by the match.

Note that the conditions in the constructor and the index lookups are fast
operations. Thus they should be used whenever possible to create efficient
matchers.

Finally, the conditions in the loop narrow down the remaining list of cells. For
performance reasons they should only be used for things that can't be done in
the constructor or with an index.

The call to the next stage with ``mul`` set to ``nullptr`` after the loop marks
an optional match. That is, the matcher will also explore the case where ``mul``
is set to ``nullptr``. Without it a match may only be assigned ``nullptr`` when
its guard evaluates to ``false``.

Making that call only when no candidate passed the conditions in the loop marks
a semioptional match: one that must match if at least one matching cell exists,
but if no matching cell exists it is set to ``nullptr``. The stage ``tail`` in
`Declaring a subpattern`_ is an example.

Slices and choices
------------------

Cell matches can contain "slices" and "choices". Slices can be used to create
matches for different sections of a cell. The slice index is stored next to the
cell in the index:

.. literalinclude:: ../../../../tests/unit/kernel/matcherDocTest.cc
   :language: cpp
   :tab-width: 4
   :start-after: [pmux_slice]
   :end-before: [/pmux_slice]
   :dedent:

The constructor adds one entry per slice:

.. literalinclude:: ../../../../tests/unit/kernel/matcherDocTest.cc
   :language: cpp
   :tab-width: 4
   :start-at: if (cell->type == ID($pmux))
   :end-before: if (cell->type == ID($ne))
   :dedent:

and the match stage can copy the slice index into a state variable so that
later matches and/or code stages can refer to it:

.. literalinclude:: ../../../../tests/unit/kernel/matcherDocTest.cc
   :language: cpp
   :tab-width: 4
   :start-after: [match_pmux]
   :end-before: [/match_pmux]
   :dedent:

A similar mechanism is "choices", where the constructor iterates over a list of
options:

.. literalinclude:: ../../../../tests/unit/kernel/matcherDocTest.cc
   :language: cpp
   :tab-width: 4
   :start-after: [ne_choice]
   :end-before: [/ne_choice]
   :dedent:

.. literalinclude:: ../../../../tests/unit/kernel/matcherDocTest.cc
   :language: cpp
   :tab-width: 4
   :start-at: if (cell->type == ID($ne))
   :end-before: if (cell->type == ID($eq))
   :dedent:

.. literalinclude:: ../../../../tests/unit/kernel/matcherDocTest.cc
   :language: cpp
   :tab-width: 4
   :start-after: [match_ne]
   :end-before: [/match_ne]
   :dedent:

Notice how additional values like ``BA`` can be stored next to the loop
variables of slices and choices.

Additional code
---------------

Interleaved with match stages there may be code stages. A code stage copies the
``Match`` before modifying state variables and ends by calling the next stage.
For example:

.. literalinclude:: ../../../../tests/unit/kernel/matcherDocTest.cc
   :language: cpp
   :tab-width: 4
   :start-after: [code_width]
   :end-before: [/code_width]
   :dedent:

Returning without calling the next stage rejects the current state and
backtracks. Similarly, ``accept(n)`` accepts the current state. (``accept`` will
not backtrack. This means it continues with the current branch and may accept a
larger match later.) It returns ``true`` when the stage must return, for example
because the callback blacklisted a matched cell. For example:

.. literalinclude:: ../../../../tests/unit/kernel/matcherDocTest.cc
   :language: cpp
   :tab-width: 4
   :start-after: [code_check]
   :end-before: [/code_check]
   :dedent:

``finish()`` terminates the current pattern matcher run. The stage must return
after calling it.

Calling the next stage more than once explores different cases. After each such
call that is followed by more code, the stage must return if ``unwinding()`` is
``true``. For example:

.. literalinclude:: ../../../../tests/unit/kernel/matcherDocTest.cc
   :language: cpp
   :tab-width: 4
   :start-after: [code_extend_body]
   :end-before: [/code_extend_body]
   :dedent:

Code that should run during backtracking, for example to maintain user data
state or to print debug messages, is written after the calls to the next stage.
If the stage can return early, like ``code_extend_body`` above, those calls go
into a separate function, so that the code after it always runs:

.. literalinclude:: ../../../../tests/unit/kernel/matcherDocTest.cc
   :language: cpp
   :tab-width: 4
   :start-after: [code_extend]
   :end-before: [/code_extend]
   :dedent:

Declaring a subpattern
----------------------

A subpattern is a sequence of stages starting with a function named after the
subpattern. Subpatterns are called from a code stage like any other stage.

Arguments are passed to subpatterns via state variables. For example,
``code_extend_body`` above passes the port to follow in ``portAB`` to the
subpattern ``tail``:

.. literalinclude:: ../../../../tests/unit/kernel/matcherDocTest.cc
   :language: cpp
   :tab-width: 4
   :start-after: [tail]
   :end-before: [/tail]
   :dedent:

Subpatterns can be called recursively. Here ``tail`` calls ``code_extend``,
which calls ``tail`` again for the inputs of the next cell.

Generating test cases
---------------------

A match stage may end with a section that is used for automatic test-case
generation, like the end of ``tail`` above:

.. literalinclude:: ../../../../tests/unit/kernel/matcherDocTest.cc
   :language: cpp
   :tab-width: 4
   :start-at: if (should_generate(
   :lines: 1-6
   :dedent:

Here ``found_any_match`` is a ``bool`` local that the stage sets to ``true``
inside its loop whenever a candidate passes the conditions.

The expression ``rng(n)`` returns a non-negative integer less than ``n``.

The second argument to ``should_generate`` is the chance of this section being
executed when the match stage did not match anything, in percent.

The third argument to ``should_generate`` is the chance of this section being
executed when the match stage did match something, in percent.

``finish(); return;`` can be used within this section to terminate the current
pattern matcher run.

``should_generate`` always returns ``false`` unless ``ctx.generate_mode`` is
set. ``test_pmgen -generate`` sets it for the patterns it supports, see
``passes/pmgen/generate.h``.
