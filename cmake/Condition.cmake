# Syntax:
#
# 	condition(<var> <expr>...)
#
# If `<expr>...` is truthful (evaluated as in `if()`) then assigns 1 to `<var>`, else assigns 0.
# The assigned value is `0`/`1` rather than `TRUE`/`FALSE` for ease of use in generator expressions.
# Note that `<expr>...` *must* be unquoted.
#
# To understand how a certain outcome is reached, reconfigure the project with `--log-level VERBOSE`.
#
# Believe it or not, CMake doesn't have this built in!
#
macro(condition var)
	if (${ARGN})
		set(${var} 1)
	else()
		set(${var} 0)
	endif()

	set(_debug_expr)
	foreach (token ${ARGN})
		if (DEFINED ${token})
			if (${${token}})
				list(APPEND _debug_expr "${token}:1")
			else()
				list(APPEND _debug_expr "${token}:0")
			endif()
		else()
			list(APPEND _debug_expr "${token}")
		endif()
	endforeach()
	string(JOIN " " _debug_expr ${_debug_expr})
	message(VERBOSE "  ${var} = ${${var}} (${_debug_expr})")
	unset(_debug_expr)
endmacro()
