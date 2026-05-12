include(CMakePushCheckState)
include(CheckSourceCompiles)
include(CheckCXXSymbolExists)

function(check_glob)
	check_cxx_symbol_exists(glob "glob.h" HAVE_GLOB)
	return (PROPAGATE HAVE_BLOB)
endfunction()

function(check_pthread_create)
	if (Threads_FOUND)
		# On WASI, `pthread_create()` is always available, but always fails on triples without threading
		# support. Probe for it while requesting the stub implementation to be hidden, otherwise we will
		# end up always crashing at runtime on thread creation.
		cmake_push_check_state(RESET)
			set(CMAKE_REQUIRED_DEFINITIONS -D_WASI_STRICT_PTHREAD)
			set(CMAKE_REQUIRED_LIBRARIES ${CMAKE_THREAD_LIBS_INIT})
			check_source_compiles(CXX [[
				#include <pthread.h>
				int main() {
					pthread_create(0, 0, 0, 0);
				}
			]] HAVE_PTHREAD_CREATE)
		cmake_pop_check_state()
	endif()
	return (PROPAGATE HAVE_PTHREAD_CREATE)
endfunction()

function(check_system)
	check_cxx_symbol_exists(system "stdlib.h" HAVE_SYSTEM)
endfunction()

function(check_popen)
	check_cxx_symbol_exists(popen "stdio.h" HAVE_POPEN)
endfunction()
