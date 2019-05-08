Pattern Matcher Generator
=========================

The program `pmgen.py` reads a `.pmg` (Pattern Matcher Generator) file and
writes a header-only C++ library that implements that pattern matcher.

The "patterns" in this context are subgraphs in a Yosys RTLIL netlist.

The algorithm used in the generated pattern matcher is a simple recursive
search with backtracking. It is left to the author of the `.pmg` file to
determine an efficient cell order for the search that allows for maximum
use of indices and early backtracking.


API of Generated Matcher
========================

When `pmgen.py` reads a `foobar.pmg` file, it writes `foobar_pm.h` containing
a class `foobar_pm`. That class is instantiated with an RTLIL module and a
list of cells from that module:

    foobar_pm pm(module, module->selected_cells());

The caller must make sure that none of the cells in the 2nd argument are
deleted for as long as the patter matcher instance is used.

At any time it is possible to disable cells, preventing them from showing
up in any future matches:

    pm.blacklist(some_cell);

The `.run_<pattern_name>(callback_function)` method searches for all matches
for the pattern`<pattern_name>` and calls the callback function for each found
match:

    pm.run_foobar([&](){
        log("found matching 'foo' cell: %s\n", log_id(pm.st.foo));
        log("          with 'bar' cell: %s\n", log_id(pm.st.bar));
    });

The `.pmg` file declares matcher state variables that are accessible via the
`.st_<pattern_name>.<state_name>` members. (The `.st_<pattern_name>` member is
of type `foobar_pm::state_<pattern_name>_t`.)

Similarly the `.pmg` file declares user data variables that become members of
`.ud_<pattern_name>`, a struct of type `foobar_pm::udata_<pattern_name>_t`.

There are four versions of the `run_<pattern_name>()` method: Without callback,
callback without arguments, callback with reference to `pm`, and callback with
reference to `pm.st_<pattern_name>`.


The .pmg File Format
====================

The `.pmg` file format is a simple line-based file format. For the most part
lines consist of whitespace-separated tokens.

Lines in `.pmg` files starting with `//` are comments.

Declaring a pattern
-------------------

A `.pmg` file contains one or more patterns. Each pattern starts with a line
with the `pattern` keyword followed by the name of the pattern.

Declaring state variables
-------------------------

One or more state variables can be declared using the `state` statement,
followed by a C++ type in angle brackets, followed by a whitespace separated
list of variable names. For example:

    state <bool> flag1 flag2 happy big
    state <SigSpec> sigA sigB sigY

State variables are automatically managed by the generated backtracking algorithm
and saved and restored as needed.

They are automatically initialized to the default constructed value of their type
when `.run_<pattern_name>(callback_function)` is called.

Declaring udata variables
-------------------------

Udata (user-data) variables can be used for example to configure the matcher or
the callback function used to perform actions on found matches.

There is no automatic management of udata variables. For this reason it is
recommended that the user-supplied matcher code treats them as read-only
variables.

They are declared like state variables, just using the `udata` statement:

    udata <int> min_data_width max_data_width
    udata <IdString> data_port_name

They are automatically initialized to the default constructed value of their type
when the pattern matcher object is constructed.

Embedded C++ code
-----------------

Many statements in a `.pmg` file contain C++ code. However, there are some
slight additions to regular C++/Yosys/RTLIL code that make it a bit easier to
write matchers:

- Identifiers starting with a dollar sign or backslash are automatically
  converted to special IdString variables that are initialized when the
  matcher object is constructed.

- The `port(<cell>, <portname>)` function is a handy alias for
  `sigmap(<cell>->getPort(<portname>))`.

- Similarly `param(<cell>, <paramname>)` looks up a parameter on a cell.

- The function `nusers(<sigspec>)` returns the number of different cells
  connected to any of the given signal bits, plus one if any of the signal
  bits is also a primary input or primary output.

- In `code..endcode` blocks there exist `accept`, `reject`, and `branch`
  statements.

- In `index` statements there is a special `===` operator for the index
  lookup.

Matching cells
--------------

Cells are matched using `match..endmatch` blocks. For example:

    match mul
        if ff
        select mul->type == $mul
        select nusers(port(mul, \Y) == 2
        index <SigSpec> port(mul, \Y) === port(ff, \D)
        filter some_weird_function(mul) < other_weird_function(ff)
        optional
    endmatch

A `match` block starts with `match <statevar>` and implicitly generates
a state variable `<statevar>` of type `RTLIL::Cell*`.

All statements in the match block are optional. (An empty match block
would simply match each and every cell in the module.)

The `if <expression>` statement makes the match block conditional. If
`<expression>` evaluates to `false` then the match block will be ignored
and the corresponding state variable is set to `nullptr`. In our example
we only try to match the `mul` cell if the `ff` state variable points
to a cell. (Presumably `ff` is provided by a prior `match` block.)

The `select` lines are evaluated once for each cell when the matcher is
initialized. A `match` block will only consider cells for which all `select`
expressions evaluated to `true`. Note that the state variable corresponding to
the match (in the example `mul`) is the only state variable that may be used
in `select` lines.

Index lines are using the `index <type> expr1 === expr2` syntax.  `expr1` is
evaluated during matcher initialization and the same restrictions apply as for
`select` expressions. `expr2` is evaluated when the match is calulated. It is a
function of any state variables assigned to by previous blocks. Both expression
are converted to the given type and compared for equality. Only cells for which
all `index` statements in the block pass are considered by the match.

Note that `select` and `index` are fast operations. Thus `select` and `index`
should be used whenever possible to create efficient matchers.

Finally, `filter <expression>` narrows down the remaining list of cells. For
performance reasons `filter` statements should only be used for things that
can't be done using `select` and `index`.

The `optional` statement marks optional matches. That is, the matcher will also
explore the case where `mul` is set to `nullptr`. Without the `optional`
statement a match may only be assigned nullptr when one of the `if` expressions
evaluates to `false`.

Additional code
---------------

Interleaved with `match..endmatch` blocks there may be `code..endcode` blocks.
Such a block starts with the keyword `code` followed by a list of state variables
that the block may modify. For example:

    code addAB sigS
        if (addA) {
            addAB = addA;
            sigS = port(addA, \B);
        }
        if (addB) {
            addAB = addB;
            sigS = port(addB, \A);
        }
    endcode

The special keyword `reject` can be used to reject the current state and
backtrack. For example:

    code
        if (ffA && ffB) {
            if (port(ffA, \CLK) != port(ffB, \CLK))
                reject;
            if (param(ffA, \CLK_POLARITY) != param(ffB, \CLK_POLARITY))
                reject;
        }
    endcode

Similarly, the special keyword `accept` can be used to accept the current
state. (`accept` will not backtrack. This means it continues with the current
branch and may accept a larger match later.)

The special keyword `branch` can be used to explore different cases. Note that
each code block has an implicit `branch` at the end. So most use-cases of the
`branch` keyword need to end the block with `reject` to avoid the implicit
branch at the end. For example:

    state <int> mode

    code mode
        for (mode = 0; mode < 8; mode++)
            branch;
        reject;
    endcode

But in some cases it is more natural to utilize the implicit branch statement:

    state <IdString> portAB

    code portAB
        portAB = \A;
        branch;
        portAB = \B;
    endcode

There is an implicit `code..endcode` block at the end of each `.pmg` file
that just accepts everything that gets all the way there.
