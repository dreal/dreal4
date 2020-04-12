cmake_minimum_required(VERSION 3.10)

# Check dynamic_bitset
if(NOT TARGET dynamic_bitset)
	message(FATAL_ERROR "dynamic_bitset target required for the docs")
endif()

# Find Doxygen
find_package(Doxygen QUIET)
if(DOXYGEN_FOUND)
	message(STATUS "Doxygen ${DOXYGEN_VERSION} found")
else()
	message(WARNING "Doxygen not found, dynamic_bitset_docs target not generated")
	return()
endif()

# Configure Doxygen
set(DOXYGEN_GENERATE_TREEVIEW YES)
#set(DOXYGEN_DISABLE_INDEX YES)
set(DOXYGEN_GENERATE_HTML YES)
set(DOXYGEN_GENERATE_LATEX NO)
set(DOXYGEN_GENERATE_XML NO)
set(DOXYGEN_FULL_PATH_NAMES YES)
set(DOXYGEN_STRIP_FROM_PATH "${CMAKE_CURRENT_SOURCE_DIR}/../include")
set(DOXYGEN_ALIASES "\"complexity=@par Complexity^^\"")
set(DOXYGEN_OUTPUT_LANGUAGE "English")
set(DOXYGEN_MARKDOWN_SUPPORT YES)

# Set files and generate target
set(DOXYGEN_USE_MDFILE_AS_MAINPAGE README.md)
doxygen_add_docs(dynamic_bitset_docs
	"${CMAKE_CURRENT_SOURCE_DIR}/../include/dynamic_bitset.hpp"
	"${CMAKE_CURRENT_SOURCE_DIR}/../README.md"
	COMMENT "Generate dynamic_bitset docs"
)
