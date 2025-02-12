add_library(yosys_passes_cmds INTERFACE)

target_sources(yosys_passes_cmds INTERFACE
    add.cc
    autoname.cc
    blackbox.cc
    box_derive.cc
    bugpoint.cc
    check.cc
    chformal.cc
    chtype.cc
    clean_zerowidth.cc
    connect.cc
    connwrappers.cc
    copy.cc
    cover.cc
    delete.cc
    design.cc
    dft_tag.cc
    edgetypes.cc
    example_dt.cc
    exec.cc
    future.cc
    glift.cc
    internal_stats.cc
    logcmd.cc
    logger.cc
    ltp.cc
    plugin.cc
    portarcs.cc
    portlist.cc
    printattrs.cc
    rename.cc
    scatter.cc
    scc.cc
    scratchpad.cc
    select.cc
    setattr.cc
    setenv.cc
    setundef.cc
    show.cc
    splice.cc
    splitcells.cc
    splitnets.cc
    sta.cc
    stat.cc
    tee.cc
    torder.cc
    trace.cc
    viz.cc
    wrapcell.cc
    write_file.cc
    xprop.cc
)

target_link_libraries(yosys PRIVATE yosys_passes_cmds)
