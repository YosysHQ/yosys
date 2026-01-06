import sys
import argparse
import os
import smtio
import re

class SExprParserError(Exception):
    pass

class SExprParser:
    def __init__(self):
        self.peekbuf = None
        self.stack = [[]]
        self.atom_pattern = re.compile(r'[a-zA-Z0-9~!@$%^&*_\-+=<>.?/#]+')
    def parse_line(self, line):
        ptr = 0
        while ptr < len(line):
            if line[ptr].isspace():
                ptr += 1
            elif line[ptr] == ';':
                break
            elif line[ptr] == '(':
                ptr += 1
                self.stack.append([])
            elif line[ptr] == ')':
                ptr += 1
                assert len(self.stack) > 1, "too many closed parentheses"
                v = self.stack.pop()
                self.stack[-1].append(v)
            else:
                match = self.atom_pattern.match(line, ptr)
                if match is None:
                    raise SExprParserError(f"invalid character '{line[ptr]}' in line '{line}'")
                start, ptr = match.span()
                self.stack[-1].append(line[start:ptr])
    def finish(self):
        assert len(self.stack) == 1, "too many open parentheses"
    def retrieve(self):
        rv, self.stack[0] = self.stack[0], []
        return rv

def simulate_smt_with_smtio(smt_file_path, vcd_path, smt_io, num_steps, rnd):
    inputs = {}
    outputs = {}
    states = {}

    def handle_datatype(lst):
        print(lst)
        datatype_name = lst[1]
        declarations = lst[2][0][1:]  # Skip the first item (e.g., 'mk_inputs')
        if datatype_name.endswith("_Inputs"):
            for declaration in declarations:
                input_name = declaration[0]
                bitvec_size = declaration[1][2]
                assert input_name.startswith("gold_Inputs_")
                inputs[input_name[len("gold_Inputs_"):]] = int(bitvec_size)
        elif datatype_name.endswith("_Outputs"):
            for declaration in declarations:
                output_name = declaration[0]
                bitvec_size = declaration[1][2]
                assert output_name.startswith("gold_Outputs_")
                outputs[output_name[len("gold_Outputs_"):]] = int(bitvec_size)
        elif datatype_name.endswith("_State"):
            for declaration in declarations:
                state_name = declaration[0]
                assert state_name.startswith("gold_State_")
                if declaration[1][0] == "_":
                    states[state_name[len("gold_State_"):]] = int(declaration[1][2])
                else:
                    states[state_name[len("gold_State_"):]] = (declaration[1][1][2], declaration[1][2][2])

    parser = SExprParser()
    with open(smt_file_path, 'r') as smt_file:
        for line in smt_file:
            parser.parse_line(line)
            for expr in parser.retrieve():
                smt_io.write(smt_io.unparse(expr))
                if expr[0] == "declare-datatype":
                    handle_datatype(expr)
                    
    parser.finish()
    assert smt_io.check_sat() == 'sat'

    def set_step(inputs, step):
        # This function assumes 'inputs' is a dictionary like {"A": 5, "B": 4}
        # and 'input_values' is a dictionary like {"A": 5, "B": 13} specifying the concrete values for each input.
        
        mk_inputs_parts = []
        for input_name, width in inputs.items():
            value = rnd.getrandbits(width)  # Generate a random number up to the maximum value for the bit size
            binary_string = format(value, '0{}b'.format(width))  # Convert value to binary with leading zeros
            mk_inputs_parts.append(f"#b{binary_string}")

        mk_inputs_call = "gold_Inputs " + " ".join(mk_inputs_parts)
        return [
            f"(define-const test_inputs_step_n{step} gold_Inputs ({mk_inputs_call}))\n",
            f"(define-const test_results_step_n{step} (Pair gold_Outputs gold_State) (gold test_inputs_step_n{step} test_state_step_n{step}))\n",
            f"(define-const test_outputs_step_n{step} gold_Outputs (first test_results_step_n{step}))\n",
            f"(define-const test_state_step_n{step+1} gold_State (second test_results_step_n{step}))\n",
        ]

    smt_commands = [f"(define-const test_state_step_n0 gold_State gold-initial)\n"]
    for step in range(num_steps):
        for step_command in set_step(inputs, step):
            smt_commands.append(step_command)

    for command in smt_commands:
        smt_io.write(command)

    assert smt_io.check_sat() == 'sat'

    # Store signal values
    signals = {name: [] for name in list(inputs.keys()) + list(outputs.keys())}
    # Retrieve and print values for each state
    def hex_to_bin(value):
        if value.startswith('x'):
            hex_value = value[1:]  # Remove the 'x' prefix
            bin_value = bin(int(hex_value, 16))[2:]  # Convert to binary and remove the '0b' prefix
            return f'b{bin_value.zfill(len(hex_value) * 4)}'  # Add 'b' prefix and pad with zeros
        return value

    combined_assertions = []
    for step in range(num_steps):
        print(f"Values for step {step + 1}:")
        for input_name, width in inputs.items():
            value = smt_io.get(f'(gold_Inputs_{input_name} test_inputs_step_n{step})')
            value = hex_to_bin(value[1:])
            print(f"  {input_name}: {value}")        
            signals[input_name].append((step, value))
        for output_name, width in outputs.items():
            value = smt_io.get(f'(gold_Outputs_{output_name} test_outputs_step_n{step})')
            value = hex_to_bin(value[1:])
            print(f"  {output_name}: {value}")
            signals[output_name].append((step, value))
            combined_assertions.append(f'(= (gold_Outputs_{output_name} test_outputs_step_n{step}) #{value})')
    # Create a single assertion covering all timesteps
    combined_condition = " ".join(combined_assertions)
    smt_io.write(f'(assert (not (and {combined_condition})))')

    # Check the combined assertion
    assert smt_io.check_sat(["unsat"]) == "unsat"

    def write_vcd(filename, signals, timescale='1 ns', date='today'):
        with open(filename, 'w') as f:
            # Write the header
            f.write(f"$date\n    {date}\n$end\n")
            f.write(f"$timescale {timescale} $end\n")
            
            # Declare signals
            f.write("$scope module gold $end\n")
            for signal_name, changes in signals.items():
                signal_size = len(changes[0][1])
                f.write(f"$var wire {signal_size - 1} {signal_name} {signal_name} $end\n")
            f.write("$upscope $end\n")
            f.write("$enddefinitions $end\n")
            
            # Collect all unique timestamps
            timestamps = sorted(set(time for changes in signals.values() for time, _ in changes))
            
            # Write initial values
            f.write("#0\n")
            for signal_name, changes in signals.items():
                for time, value in changes:
                    if time == 0:
                        f.write(f"{value} {signal_name}\n")
            
            # Write value changes
            for time in timestamps:
                if time != 0:
                    f.write(f"#{time}\n")
                    for signal_name, changes in signals.items():
                        for change_time, value in changes:
                            if change_time == time:
                                f.write(f"{value} {signal_name}\n")


    write_vcd(vcd_path, signals)

def simulate_smt(smt_file_path, vcd_path, num_steps, rnd):
    so = smtio.SmtOpts()
    so.solver = "z3"
    so.logic = "ABV"
    so.debug_print = True
    smt_io = smtio.SmtIo(opts=so)
    try:
        simulate_smt_with_smtio(smt_file_path, vcd_path, smt_io, num_steps, rnd)
    finally:
        smt_io.p_close()