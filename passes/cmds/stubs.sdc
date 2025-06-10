# with Tcl's eager evaluation, we will still eval args if they're unused by a stub
proc stub {function_name} {
    proc $function_name {args} "puts \"stubbed $function_name\""
}

proc is_suppressed {args} {
    return 0
}

proc create_clock {args} {
    return "CLOCK@"
}
proc get_clocks {args} {
    return "CLOCK@"
}

stub current_design
stub ys_track_typed_key
stub ys_track_untyped_key
stub ys_err_key
stub ys_err_flag
