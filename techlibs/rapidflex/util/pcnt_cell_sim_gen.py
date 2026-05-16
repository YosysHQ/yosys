#####################################################################
# A script to generate cell sim for pcounters
#####################################################################
import os
from os.path import dirname, abspath
import argparse
import logging
import csv
import pcounter_ip_template_generator

#####################################################################
# Error codes
#####################################################################
error_codes = {"SUCCESS": 0, "ERROR": 1, "FILE_ERROR": 3}

#####################################################################
# Initialize logger
#####################################################################
logging.basicConfig(format="%(levelname)s: %(message)s", level=logging.INFO)


def generate_file_header(f0):
    f0.write("//-------------------------------------------------\n")
    f0.write("// IMPORTANT: This file is auto generated!!! DO NOT MODIFY BY HAND!!!\n")
    f0.write("//-------------------------------------------------\n")
    f0.write("// Pcounter Primitives\n")
    f0.write("// Naming convention:\n")
    f0.write(
        "//   pcounter<size>_clk<trigger_type>_<reset_type>rst<reset_poloarity>_<event_function>\n"
    )
    f0.write(
        "// size: [N | <int> ] ranges from 0 to 31, representing the number of bits. N is a parameterized design, which is supposed not be exposed to users\n"
    )
    f0.write("// trigger_type: [p|n] denotes [rising edge (posedge) | falling edge (negedge) ]\n")
    f0.write("// reset_type: [a|s] denotes [ asynchronous | synchronous ]\n")
    f0.write("// reset_polarity: [p|n] denotes [ active-high | active-low ]\n")
    f0.write(
        "// event_function : [ load | add | sub | sr | sl ] denotes [ load | add | substract | shift right | shift left ] on the data_i values\n"
    )


def generate_pcounter_ips(fpath):
    pcnt_ip_tmpl_gen = pcounter_ip_template_generator.PcounterIpTemplateGenerator()
    cnt = 0
    with open(fpath, "w") as cell_sim_fh:
        generate_file_header(cell_sim_fh)
        for clk_type in pcnt_ip_tmpl_gen.clock_types():
            for rst_type in pcnt_ip_tmpl_gen.reset_types():
                for rst_polar in pcnt_ip_tmpl_gen.reset_polarities():
                    for event_type in pcnt_ip_tmpl_gen.event_types():
                        logging.info(
                            f"Generating IPs: {pcnt_ip_tmpl_gen.ip_template_name(clk_type, rst_type, rst_polar, event_type)} ..."
                        )
                        logging.debug(
                            f"Generating IP template: {pcnt_ip_tmpl_gen.ip_template_name(clk_type, rst_type, rst_polar, event_type)} ..."
                        )
                        pcnt_ip_tmpl_gen.write_ip_template(
                            cell_sim_fh, clk_type, rst_type, rst_polar, event_type
                        )
                        logging.debug(f"Done")
                        cnt += 1
                        # Generate full-size (32-bit) version
                        d_size = pcnt_ip_tmpl_gen.max_data_size()
                        logging.debug(
                            f"Generating full-sized counter IP: {pcnt_ip_tmpl_gen.ip_name(clk_type, rst_type, rst_polar, event_type, d_size)} ..."
                        )
                        pcnt_ip_tmpl_gen.write_ip(
                            cell_sim_fh, clk_type, rst_type, rst_polar, event_type, d_size
                        )
                        logging.debug(f"Done")
                        cnt += 1
                        # Generate half-size (16-bit) version
                        d_size = int(pcnt_ip_tmpl_gen.max_data_size() / 2)
                        logging.debug(
                            f"Generating half-sized counter IP: {pcnt_ip_tmpl_gen.ip_name(clk_type, rst_type, rst_polar, event_type, d_size)} ..."
                        )
                        pcnt_ip_tmpl_gen.write_ip(
                            cell_sim_fh, clk_type, rst_type, rst_polar, event_type, d_size
                        )
                        logging.debug(f"Done")
                        cnt += 1
                        # Generate CCB
                        logging.info(
                            f"Generating ccb-related IPs: {pcnt_ip_tmpl_gen.ccb_ip_template_name(clk_type, rst_type, rst_polar, event_type)} ..."
                        )
                        logging.debug(
                            f"Generating ccb-related IP template: {pcnt_ip_tmpl_gen.ccb_ip_template_name(clk_type, rst_type, rst_polar, event_type)} ..."
                        )
                        pcnt_ip_tmpl_gen.write_ccb_ip_template(
                            cell_sim_fh, clk_type, rst_type, rst_polar, event_type
                        )
                        logging.debug(f"Done")
                        cnt += 1
                        d_size = pcnt_ip_tmpl_gen.max_data_size()
                        logging.debug(
                            f"Generating ccb-related full-sized IP: {pcnt_ip_tmpl_gen.ccb_ip_name(clk_type, rst_type, rst_polar, event_type, d_size)} ..."
                        )
                        pcnt_ip_tmpl_gen.write_ccb_ip(
                            cell_sim_fh, clk_type, rst_type, rst_polar, event_type, d_size
                        )
                        logging.debug(f"Done")
                        cnt += 1
                        # Generate half-size (16-bit) version
                        d_size = int(pcnt_ip_tmpl_gen.max_data_size() / 2)
                        logging.debug(
                            f"Generating ccb-related half-sized IP: {pcnt_ip_tmpl_gen.ccb_ip_name(clk_type, rst_type, rst_polar, event_type, d_size)} ..."
                        )
                        pcnt_ip_tmpl_gen.write_ccb_ip(
                            cell_sim_fh, clk_type, rst_type, rst_polar, event_type, d_size
                        )
                        logging.debug(f"Done")
                        cnt += 1
                        logging.info(f"Done")

    logging.info(f"Generated {cnt} IPs")

    return 0


#####################################################################
# Main function
#####################################################################
if __name__ == "__main__":
    # Execute when the module is not initialized from an import statement

    # Parse the options and apply sanity checks
    parser = argparse.ArgumentParser(description="Generate cell sim Verilog for Pcounter")
    parser.add_argument(
        "--file",
        required=True,
        default="cell_sim_pcnt.v",
        help="Path to the .v file that contains pcounter IPs",
    )
    args = parser.parse_args()

    num_error = generate_pcounter_ips(args.file)
    if num_error == 0:
        logging.info("Generation succeed")
        exit(error_codes["SUCCESS"])
    else:
        logging.error("Generation failed in " + str(num_error) + " errors!")
        exit(error_codes["ERROR"])
