import sys
import argparse
import random
import os

# Parse command line arguments
parser = argparse.ArgumentParser(description='Process SMT file for simulation.')
parser.add_argument('smt_file', help='Path to the SMT file to simulate.')
args = parser.parse_args()

# Get the SMT file path from the command line argument
smt_file_path = args.smt_file
current_file_path = os.path.abspath(__file__)
# Navigate to the directory you need relative to the current script
# Assuming 'backends/smt2' is located three directories up from the current script
desired_path = os.path.join(os.path.dirname(current_file_path), '..', '..', '..', 'backends', 'functional')

# Normalize the path to resolve any '..'
normalized_path = os.path.normpath(desired_path)

# Append the directory to the Python path
sys.path.append(normalized_path)

# Import the module
import smtio

# Assuming the SmtIo class and other dependencies are available in your environment
# You may need to include the entire script provided above in your script or have it available as a module

# Step 1: Initialize an SmtIo object

so = smtio.SmtOpts()
so.solver = "z3"
so.logic = "BV"
so.debug_print = True
# so.debug_file = "my_debug"
smt_io = smtio.SmtIo(opts=so)
# List to store the parsed results
parsed_results = []

# Load and execute the SMT file
with open(smt_file_path, 'r') as smt_file:
    for line in smt_file:
        smt_io.write(line.strip())    
smt_io.check_sat()
# Read and parse the SMT file line by line
with open(smt_file_path, 'r') as smt_file:
    for line in smt_file:
        # Strip leading/trailing whitespace
        stripped_line = line.strip()
        
        # Ignore empty lines
        if not stripped_line:
            continue
        # comments
        if stripped_line.startswith(';'):
            smt_io.info(stripped_line)
        
        # Parse the line using SmtIo's parse method
        parsed_line = smt_io.parse(stripped_line)
        
        # Append the parsed result to the list
        parsed_results.append(parsed_line)

# Display the parsed results
for result in parsed_results:
    print(result)

inputs = {}
outputs = {}

for lst in parsed_results:
    if lst[0] == 'declare-datatypes':
        for datatype_group in lst[2]:  # Navigate into the nested lists
            datatype_name = datatype_group[0]
            declarations = datatype_group[1][1:]  # Skip the first item (e.g., 'mk_inputs')
            if datatype_name == 'Inputs':
                for declaration in declarations:
                    input_name = declaration[0]
                    bitvec_size = declaration[1][2]
                    inputs[input_name] = int(bitvec_size)
            elif datatype_name == 'Outputs':
                for declaration in declarations:
                    output_name = declaration[0]
                    bitvec_size = declaration[1][2]
                    outputs[output_name] = int(bitvec_size)
    
print(inputs)
print(outputs)
def set_step(inputs, step):
    # This function assumes 'inputs' is a dictionary like {"A": 5, "B": 4}
    # and 'input_values' is a dictionary like {"A": 5, "B": 13} specifying the concrete values for each input.
    
    # Construct input definitions
    mk_inputs_parts = []
    for input_name, width in inputs.items():
        value = random.getrandbits(width)  # Generate a random number up to the maximum value for the bit size
        binary_string = format(value, '0{}b'.format(width))  # Convert value to binary with leading zeros
        mk_inputs_parts.append(f"#b{binary_string}")

    # Join all parts for the mk_inputs constructor
    mk_inputs_call = "mk_inputs " + " ".join(mk_inputs_parts)
    define_inputs = f"(define-const test_inputs_step_n{step} Inputs ({mk_inputs_call}))\n"

    # Create the output definition by calling the gold_step function
    define_output = f"(define-const test_outputs_step_n{step} Outputs (gold_step #b0 test_inputs_step_n{step}))\n"
    smt_commands = []
    smt_commands.append(define_inputs)
    smt_commands.append(define_output)
    return smt_commands

num_steps = 10
smt_commands = []
# Loop to generate SMT commands for each step
for step in range(num_steps):
    for step_command in set_step(inputs, step):
        smt_commands.append(step_command)

# Print or write the SMT commands to a file
smt_file_content = ''.join(smt_commands)
print(smt_file_content)  # Print to console

# Optionally, write to a file
with open('dynamic_commands.smt2', 'w') as smt_file:
    smt_file.write(smt_file_content)

# Execute the SMT commands
for command in smt_commands:
    print(command)
    smt_io.write(command.strip())

# Check for satisfiability
# smt_io.setup()
result = smt_io.check_sat()
print(f'SAT result: {result}')
if result != 'sat':
    smt_io.p_close()
    sys.exit(1)

value = smt_io.get(f'(Y test_outputs_step_n0)')
print(f"  Y: {value}")

# Store signal values
signals = {name: [] for name in list(inputs.keys()) + list(outputs.keys())}
# Retrieve and print values for each state
def hex_to_bin(value):
    if value.startswith('x'):
        hex_value = value[1:]  # Remove the 'x' prefix
        bin_value = bin(int(hex_value, 16))[2:]  # Convert to binary and remove the '0b' prefix
        return f'b{bin_value.zfill(len(hex_value) * 4)}'  # Add 'b' prefix and pad with zeros
    return value
for step in range(num_steps):
    print(f"Values for step {step + 1}:")
    for input_name, width in inputs.items():
        value = smt_io.get(f'({input_name} test_inputs_step_n{step})')
        value = hex_to_bin(value[1:])
        print(f"  {input_name}: {value}")        
        signals[input_name].append((step, value))
    for output_name, width in outputs.items():
        value = smt_io.get(f'({output_name} test_outputs_step_n{step})')
        value = hex_to_bin(value[1:])
        print(f"  {output_name}: {value}")
        signals[output_name].append((step, value))
        smt_io.write(f'(push 1)')
        smt_io.write(f'(assert (not (= ({output_name} test_outputs_step_n{step}) #{value})))')
        result = smt_io.check_sat(["unsat"])
        if result != 'unsat':
            smt_io.p_close()
            sys.exit(1)
        smt_io.write(f'(pop 1)')
        result = smt_io.check_sat(["sat"])
        if result != 'sat':
            smt_io.p_close()
            sys.exit(1)
        
smt_io.p_close()

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
                            f.write(f"b{value} {signal_name}\n")


# Write the VCD file
write_vcd(smt_file_path + '.vcd', signals)
sys.exit(0)
