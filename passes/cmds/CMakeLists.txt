

add_library(yosys_passes_cmds OBJECT
    add.cc
    delete.cc
    design.cc
    select.cc
    show.cc
    viz.cc
    rename.cc
    autoname.cc
    connect.cc
    scatter.cc
    setundef.cc
    splitnets.cc
    splitcells.cc
    stat.cc
    internal_stats.cc
    setattr.cc
    copy.cc
    splice.cc
    scc.cc
    glift.cc
    torder.cc
    logcmd.cc
    tee.cc
    write_file.cc
    connwrappers.cc
    cover.cc
    trace.cc
    plugin.cc
    check.cc
    edgetypes.cc
    portlist.cc
    chformal.cc
    chtype.cc
    blackbox.cc
    ltp.cc
    scratchpad.cc
    logger.cc
    printattrs.cc
    sta.cc
    clean_zerowidth.cc
    xprop.cc
    dft_tag.cc
    future.cc
    box_derive.cc
    example_dt.cc
    portarcs.cc
    wrapcell.cc
    setenv.cc
    test_select.cc
    abstract.cc
)

if (NOT DISABLE_SPAWN)
target_sources(yosys_passes_cmds PRIVATE
    exec.cc
    bugpoint.cc
)
endif()

target_link_libraries(yosys PUBLIC yosys_passes_cmds)
target_sources(yosys PUBLIC $<TARGET_OBJECTS:yosys_passes_cmds>)
