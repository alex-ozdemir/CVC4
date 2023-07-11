find_path(Z3_INCLUDE_DIR NAMES z3++.h)
message(STATUS ${CMAKE_PREFIX_PATH})
find_library(Z3_LIBRARIES NAMES libz3.a)

set(Z3_FOUND_SYSTEM FALSE)
if(Z3_INCLUDE_DIR AND Z3_LIBRARIES)
  set(Z3_FOUND_SYSTEM TRUE)
else()
    message(FATAL_ERROR "Missing z3")
endif()
set(Z3_FOUND TRUE)

add_library(Z3 STATIC IMPORTED GLOBAL)
set_target_properties(Z3 PROPERTIES IMPORTED_LOCATION "${Z3_LIBRARIES}")
set_target_properties(
  Z3 PROPERTIES INTERFACE_SYSTEM_INCLUDE_DIRECTORIES "${Z3_INCLUDE_DIR}"
)
#set_target_properties(Z3 PROPERTIES INTERFACE_LINK_LIBRARIES GMP)

mark_as_advanced(Z3_FOUND)
mark_as_advanced(Z3_FOUND_SYSTEM)
mark_as_advanced(Z3_INCLUDE_DIR)
mark_as_advanced(Z3_LIBRARIES)

message(STATUS "Found Z3 library: ${Z3_LIBRARIES}")
message(STATUS "Found Z3 headers: ${Z3_INCLUDE_DIR}")
