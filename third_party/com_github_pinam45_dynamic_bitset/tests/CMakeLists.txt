cmake_minimum_required(VERSION 3.10) # For CXX_STANDARD 17 property on Visual Studio

# Options
option(DYNAMICBITSET_ENABLE_COVERAGE "Enable coverage informations generation" OFF)

# Check dynamic_bitset
if(NOT TARGET dynamic_bitset)
	message(FATAL_ERROR "dynamic_bitset target required for the example")
endif()

# Project declaration
project(
  dynamic_bitset_tests
  DESCRIPTION "C++ dynamic bitset tests"
  LANGUAGES CXX
)

# Declare dynamic_bitset_tests
add_executable(dynamic_bitset_tests)

# Add sources
cmutils_target_sources_folders(
  dynamic_bitset_tests PRIVATE
  "${CMAKE_CURRENT_SOURCE_DIR}/src"
  "${CMAKE_CURRENT_SOURCE_DIR}/include"
)

# Add includes
target_include_directories(
  dynamic_bitset_tests PRIVATE
  "${CMAKE_CURRENT_SOURCE_DIR}/include"
)

# Link dynamic_bitset
target_link_libraries(dynamic_bitset_tests PRIVATE dynamic_bitset)

# Link Catch2
target_link_libraries(dynamic_bitset_tests PRIVATE Catch2::Catch2)

# Configure compile options
cmutils_target_configure_compile_options(dynamic_bitset_tests)
if(DYNAMICBITSET_ENABLE_COVERAGE)
	target_compile_options(dynamic_bitset_tests PRIVATE "--coverage")
	if(COMMAND target_link_options)
		target_link_options(dynamic_bitset_tests PRIVATE "--coverage")
	else()
		# old CMake version: use ugly workaround
		__cmutils_target_link_flag_property(dynamic_bitset_tests "--coverage")
	endif()
	message(STATUS "dynamic_bitset_tests: enabled coverage")
endif()

# Enable cmutils default warnings
cmutils_target_enable_warnings(dynamic_bitset_tests)

# Build in C++17
cmutils_target_set_standard(dynamic_bitset_tests CXX 17)

# Enable sanitizers in debug
#cmutils_target_enable_sanitizers(
#  dynamic_bitset_tests
#  ADDRESS LEAK MEMORY #UNDEFINED
#  DEBUG
#)

# Set target IDE folder
cmutils_target_set_ide_folder(dynamic_bitset_tests "dynamic_bitset")

# Group sources for IDEs
cmutils_target_source_group(dynamic_bitset_tests "${CMAKE_CURRENT_SOURCE_DIR}")

# Use ccache
cmutils_target_use_ccache(dynamic_bitset_tests)

# Generate format target
cmutils_target_generate_clang_format(dynamic_bitset_tests)

# Discover tests
catch_discover_tests(dynamic_bitset_tests)
