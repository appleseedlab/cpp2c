#===============================================================================
# 1. LOAD LLVM CONFIGURATION
#===============================================================================
# Set this to a valid LLVM installation dir
set(CPP2C_LLVM_INSTALL_DIR "" CACHE PATH "LLVM installation directory")

# Add the location of ClangConfig.cmake to CMake search paths (so that
# find_package can locate it)
list(APPEND CMAKE_PREFIX_PATH "${CPP2C_LLVM_INSTALL_DIR}/lib/cmake/clang/")

find_package(Clang REQUIRED CONFIG)

# HelloWorld includes headers from LLVM and Clang - update the include paths
# accordingly
include_directories(SYSTEM "${LLVM_INCLUDE_DIRS};${CLANG_INCLUDE_DIRS}")

#===============================================================================
# 2. LLVM-TUTOR BUILD CONFIGURATION
#===============================================================================
# Use the same C++ standard as LLVM does
set(CMAKE_CXX_STANDARD 14 CACHE STRING "")

# LLVM is normally built without RTTI. Be consistent with that.
if(NOT LLVM_ENABLE_RTTI)
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fno-rtti")
endif()

set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -O1")


#===============================================================================
# 3. ADD THE TARGET
#===============================================================================
add_library(Cpp2C SHARED
  Cpp2C.cc
  CollectDeclNamesVisitor.hh
  ExpansionUtils.cc
  ExpansionUtils.hh
  ForestCollector.cc
  ForestCollector.hh
  MacroArgument.cc
  MacroArgument.hh
  MacroExpansionNode.cc
  MacroExpansionNode.hh
  MacroForest.cc
  MacroForest.hh
  MacroNameCollector.hh
  Matchers.hh
  NodeCollector.hh
  SourceRangeCollection.cc
  SourceRangeCollection.hh
  TransformedDefinition.cc
  TransformedDefinition.hh
  )

# Allow undefined symbols in shared objects on Darwin (this is the default
# behaviour on Linux)
target_link_libraries(Cpp2C
  "$<$<PLATFORM_ID:Darwin>:-undefined dynamic_lookup>")
