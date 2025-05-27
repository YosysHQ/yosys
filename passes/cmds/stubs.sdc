# with Tcl's eager evaluation, we will still eval args if they're unused by a stub
proc stub {function_name} {
    proc $function_name {args} {}
}

# OpenROAD
proc get_name {thing} {
    return thing
}
proc get_full_name {thing} {
    return thing
}

# Vivado UG903
stub add_cells_to_pblock
stub add_to_power_rail
stub all_clocks
stub all_cpus
stub all_dsps
stub all_fanin
stub all_fanout
stub all_ffs
stub all_hsios
stub all_inputs
stub all_latches
stub all_outputs
stub all_rams
stub all_registers
stub connect_debug_port
stub create_clock
stub create_debug_core
stub create_debug_port
stub create_generated_clock
stub create_macro
stub create_pblock
stub create_power_rail
stub create_property
stub create_waiver
stub current_design
stub current_instance
stub delete_macros
stub delete_pblock
stub delete_power_rails
stub endgroup
stub get_bel_pins
stub get_bels
stub get_clocks
stub get_debug_cores
stub get_debug_ports
stub get_generated_clocks
stub get_hierarchy_separator
stub get_iobanks
stub get_macros
stub get_nodes
stub get_package_pins
stub get_path_groups
stub get_pblocks
stub get_pips
stub get_pkgpin_bytegroups
stub get_pkgpin_nibbles
stub get_power_rails
stub get_property
stub get_site_pins
stub get_site_pips
stub get_sites
stub get_slrs
stub get_speed_models
stub get_tiles
stub get_timing_arcs
stub group_path
stub make_diff_pair_ports
stub remove_cells_from_pblock
stub remove_from_power_rail
stub reset_operating_conditions
stub reset_switching_activity
stub resize_pblock
stub set_bus_skew
stub set_case_analysis
stub set_clock_groups
stub set_clock_latency
stub set_clock_sense
stub set_clock_uncertainty
stub set_data_check
stub set_disable_timing
stub set_external_delay
stub set_false_path
stub set_hierarchy_separator
stub set_input_delay
stub set_input_jitter
stub set_load
stub set_logic_dc
stub set_logic_one
stub set_logic_unconnected
stub set_logic_zero
stub set_max_delay
stub set_max_time_borrow
stub set_min_delay
stub set_multicycle_path
stub set_operating_conditions
stub set_output_delay
stub set_package_pin_val
stub set_power_opt
stub set_propagated_clock
stub set_property
stub set_switching_activity
stub set_system_jitter
stub set_units
stub startgroup
stub update_macro
