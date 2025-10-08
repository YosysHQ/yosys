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
    # puts "unknown $args, returning YOSYS_SDC_MAGIC_NODE_$sdc_call_index"
    return $ret
}
proc list {args} {
    return [unknown "list" {*}$args]
}