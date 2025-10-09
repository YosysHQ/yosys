proc unknown {args} {
    # Check if it's a getter
    if {[llength $args] > 0} {
        set first_arg [lindex $args 0]
        if {[string match "get_*" $first_arg]} {
            # It's a getter, has it been redirected from specialized C++ code?
            if {[llength $args] > 1} {
                set second_arg [lindex $args 1]
                if {$second_arg ne "-getter-validated"} {
                    error "Unknown getter: $first_arg"
                }
            } else {
                error "Unknown getter: $first_arg"
            }
        }
    }
    # TODO this safety feature could be optional via a global

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
    # puts "unknown $args, returning YOSYS_SDC_MAGIC_NODE_$sdc_call_index"
    return $ret
}
proc list {args} {
    return [unknown "list" {*}$args]
}
proc get_clocks {args} {
    # get_clocks isn't a design object getter
    # because clocks aren't design objects, just aliases
    # so the referred to clock pin already are being tracked
    # as arguments of uninterpreted create_clock command or similar
    return [unknown "get_clocks" "-getter-validated" {*}$args]
}
