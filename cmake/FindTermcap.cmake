# find Terrmcap (terminal input library) includes and library
#
# TERMCAP_INCLUDE_DIR - where the directory containing the TERMCAP headers can be found
# TERMCAP_LIBRARY     - full path to the TERMCAP library
# TERMCAP_FOUND       - TRUE if TERMCAP was found

macro(find_termcap)

    find_path(TERMCAP_INCLUDE_DIR termcap.h
              /usr/include
              /usr/local/include

              /opt/local/include
              )

    find_library(TERMCAP_LIBRARY NAMES termcap PATH
                 /usr/lib
                 /usr/local/lib
                 /opt/local/lib
                 /usr/lib64
                 )

    if(TERMCAP_INCLUDE_DIR AND TERMCAP_LIBRARY)
        set(TERMCAP_FOUND TRUE)
        message(STATUS "Found GNU termcap: ${TERMCAP_LIBRARY}")
        message(STATUS "Include dir is: ${TERMCAP_INCLUDE_DIR}")
        include_directories(${TERMCAP_INCLUDE_DIR})
    else(TERMCAP_INCLUDE_DIR AND TERMCAP_LIBRARY)
        set(TERMCAP_FOUND FALSE)
        message(FATAL_ERROR "Could not find GNU termcap")
    endif(TERMCAP_INCLUDE_DIR AND TERMCAP_LIBRARY)

endmacro(find_termcap)