cmake_minimum_required(VERSION 3.10) # For CXX_STANDARD 17 property on Visual Studio

# Check dynamic_bitset
if(NOT TARGET dynamic_bitset)
	message(FATAL_ERROR "dynamic_bitset target required for the example")
endif()

# Declare dynamic_bitset_example
add_executable(dynamic_bitset_example)

# Add sources
cmutils_target_sources_folders(
  dynamic_bitset_example PRIVATE
  "${CMAKE_CURRENT_SOURCE_DIR}/src"
)

# Link dynamic_bitset
target_link_libraries(dynamic_bitset_example PRIVATE dynamic_bitset)

# Configure compile options
cmutils_target_configure_compile_options(dynamic_bitset_example)

# Enable cmutils default warnings
cmutils_target_enable_warnings(dynamic_bitset_example)

# Build in C++17
cmutils_target_set_standard(dynamic_bitset_example CXX 17)

# Enable sanitizers in debug
#cmutils_target_enable_sanitizers(
#  dynamic_bitset_example
#  ADDRESS LEAK MEMORY UNDEFINED
#  DEBUG
#)

# Set target IDE folder
cmutils_target_set_ide_folder(dynamic_bitset_example "dynamic_bitset")

# Group sources for IDEs
cmutils_target_source_group(dynamic_bitset_example "${CMAKE_CURRENT_SOURCE_DIR}")

# Visual studio config
set_property(
  DIRECTORY
  ${CMAKE_CURRENT_SOURCE_DIR} PROPERTY
  VS_STARTUP_PROJECT dynamic_bitset_example
)

# Use ccache
cmutils_target_use_ccache(dynamic_bitset_example)

# Generate format target
cmutils_target_generate_clang_format(dynamic_bitset_example)
