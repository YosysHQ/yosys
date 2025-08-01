# with Tcl's eager evaluation, we will still eval args if they're unused by a stub
proc stub {function_name} {
    proc $function_name {args} "puts \"stubbed $function_name\""
}

proc is_suppressed {args} {
    return 0
}

# stub current_design
#stub ys_track_typed_key
stub ys_track_untyped_key
stub ys_err_key
stub ys_err_flag

# TODO move to separate file and tie to graph value mode
proc unknown {args} {
    global sdc_call_index
    global sdc_calls
    if {![info exists sdc_call_index]} {
        set sdc_call_index 0
    }
    if {![info exists sdc_calls]} {
        set sdc_calls {}
    }
    set ret "YOSYS_SDC_MAGIC_NODE_$sdc_call_index"
    incr sdc_call_index
    lappend sdc_calls $args
    puts "unknown $args, returning YOSYS_SDC_MAGIC_NODE_$sdc_call_index"
    return $ret
}
proc list {args} {
    return [unknown "list" {*}$args]
}