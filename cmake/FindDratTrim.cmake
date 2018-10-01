# Find drat-trim
# DratTrim_FOUND - system has DratTrim lib
# DratTrim_INCLUDE_DIR - the DratTrim include directory
# DratTrim_LIBRARIES - Libraries needed to use DratTrim


# Check default location of DratTrim built with contrib/get-drat-trim.
# If the user provides a directory we will not search the default paths and
# fail if DratTrim was not found in the specified directory.
if(NOT DratTrim_HOME)
  set(DratTrim_HOME ${PROJECT_SOURCE_DIR}/drat-trim/install)
endif()

find_path(DratTrim_INCLUDE_DIR
          NAMES drat-trim.h
          PATHS ${DratTrim_HOME}/include
          NO_DEFAULT_PATH)
find_library(DratTrim_LIBRARIES
             NAMES drat-trim.a
             PATHS ${DratTrim_HOME}/lib
             NO_DEFAULT_PATH)

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(DratTrim
  DEFAULT_MSG
  DratTrim_INCLUDE_DIR DratTrim_LIBRARIES)

mark_as_advanced(DratTrim_INCLUDE_DIR DratTrim_LIBRARIES)
if(DratTrim_LIBRARIES)
  message(STATUS "Found DratTrim libs: ${DratTrim_LIBRARIES}")
endif()
