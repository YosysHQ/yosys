#!/usr/bin/env python3
#
# yosys -- Yosys Open SYnthesis Suite
#
# Copyright (C) 2022  Jannis Harder <jix@yosyshq.com> <me@jix.one>
#
# Permission to use, copy, modify, and/or distribute this software for any
# purpose with or without fee is hereby granted, provided that the above
# copyright notice and this permission notice appear in all copies.
#
# THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
# WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
# MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
# ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
# WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
# ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
# OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
#

import os, sys
##yosys-sys-path##
import click

from ywio import ReadWitness, WriteWitness, WitnessSig

@click.group()
def cli():
    pass


@cli.command(help="""
Display a Yosys witness trace in a human readable format.
""")
@click.argument("input", type=click.File("r"))
def display(input):
    click.echo(f"Reading Yosys witness trace {input.name!r}...")
    inyw = ReadWitness(input)

    def output():

        yield click.style("*** RTLIL bit-order below may differ from source level declarations ***", fg="red")
        if inyw.clocks:
            yield click.style("=== Clock Signals ===", fg="blue")
            for clock in inyw.clocks:
                yield f"  {clock['edge']} {WitnessSig(clock['path'], clock['offset']).pretty()}"

        for t, values in inyw.steps():
            if t:
                yield click.style(f"=== Step {t} ===", fg="blue")
            else:
                yield click.style("=== Initial State ===", fg="blue")

            step_prefix = click.style(f"#{t}", fg="bright_black")

            signals, missing = values.present_signals(inyw.sigmap)

            assert not missing

            for sig in signals:
                display_bits = values[sig].replace("?", click.style("?", fg="bright_black"))
                yield f"  {step_prefix} {sig.pretty()} = {display_bits}"
    click.echo_via_pager([line + "\n" for line in output()])

@cli.command(help="""
Transform a Yosys witness trace.

Currently no transformations are implemented, so it is only useful for testing.
""")
@click.argument("input", type=click.File("r"))
@click.argument("output", type=click.File("w"))
def yw2yw(input, output):
    click.echo(f"Copying yosys witness trace from {input.name!r} to {output.name!r}...")
    inyw = ReadWitness(input)
    outyw = WriteWitness(output, "yosys-witness yw2yw")

    for clock in inyw.clocks:
        outyw.add_clock(clock["path"], clock["offset"], clock["edge"])

    for sig in inyw.signals:
        outyw.add_sig(sig.path, sig.offset, sig.width, sig.init_only)

    for t, values in inyw.steps():
        outyw.step(values)

    outyw.end_trace()

    click.echo(f"Copied {outyw.t + 1} time steps.")

if __name__ == "__main__":
    cli()
