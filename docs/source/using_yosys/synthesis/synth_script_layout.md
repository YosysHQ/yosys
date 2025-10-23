How `synth_*` scripts are laid out
-----------------------------------

At a high level, all the `synth_*` scripts are structured fairly similarly:
- a `struct` deriving from `ScriptPass`
    - which has a constructor which registers itself as a pass.
    - which overrides `help()` to display useful information when
    `help synth_*` is invoked.
    - which overrides `clear_flags()` to initialise default options.
    - which overrides `execute()` to parse options from the command line.
    - which overrides `script()` to then execute the script itself.
    - which may override `on_register()` to set scratchpad variables.
- which is then instantiated.

`help()`
========

Where possible, options are organised in groups, and ordered such
that the most commonly used options appear first. A user will find
options about output format (JSON, EDIF, BLIF, Verilog) much more
useful than options about disabling carry chains for debug purposes.

Additionally, we try to use the same or similar wording for option descriptions
across passes where possible, and aim for those descriptions to be succinct.

`script()`
==========

The `script()` function is usually organised into "labels" which define stages
to be executed or skipped. A user can choose which labels are executed using
the `-run <begin>:<end>` (begin-inclusive, end-exclusive) option.

Each command is executed with a call to `run()`. Most calls to `run` should
only need the first argument, which is the command itself.

Each label in the code looks like this:
```cpp
if (check_label("label_name")) {
    run("cmd1");
    run("cmd2");
}
```

Which looks like this in the output of `help` for your pass:
```
    label_name:
        cmd1
        cmd2
```

`help` displays the calls to `run()` without executing them. When running under
`help`, the `help_mode` variable will be set. This can be useful:
- when some passes are conditional, making sure that the passes still execute
    if `help_mode` ensures the logic is displayed to the user.
- when a pass has a lot of command line options, or ones that significantly
    vary across architecture families, the options can be hidden by calling `run`
    with an abbreviated command line if `help_mode` is active.

If passes are conditional, it's a good idea to communicate this to the user
by using the second argument of `run` to describe the condition in question.
The general wording of this is that if a pass only runs when `-foo` is passed
to the command, then the option is described with `(only if -foo)`. If it runs
except when `-foo` is passed, then the option is described with `(unless -foo)`.

