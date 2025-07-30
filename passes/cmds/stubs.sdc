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

proc unknown {args} {
    global sdc_call_index
    global sdc_calls
    if {![info exists index]} {
        set sdc_call_index 0
    }
    if {![info exists sdc_calls]} {
        set sdc_calls {}
    }
    incr sdc_call_index
    lappend sdc_calls $args
    return $sdc_call_index
}