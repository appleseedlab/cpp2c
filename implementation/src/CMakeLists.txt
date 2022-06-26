# ===============================================================================
# 1. LOAD LLVM CONFIGURATION
# ===============================================================================
# Set this to a valid LLVM installation dir
set(CPP2C_LLVM_INSTALL_DIR "" CACHE PATH "LLVM installation directory")

# Add the location of ClangConfig.cmake to CMake search paths (so that
# find_package can locate it)
list(APPEND CMAKE_PREFIX_PATH "${CPP2C_LLVM_INSTALL_DIR}/lib/cmake/clang/")

find_package(Clang REQUIRED CONFIG)

# HelloWorld includes headers from LLVM and Clang - update the include paths
# accordingly
include_directories(SYSTEM "${LLVM_INCLUDE_DIRS};${CLANG_INCLUDE_DIRS}")

# ===============================================================================
# 2. LLVM-TUTOR BUILD CONFIGURATION
# ===============================================================================
# Use the same C++ standard as LLVM does
set(CMAKE_CXX_STANDARD 14 CACHE STRING "")

# LLVM is normally built without RTTI. Be consistent with that.
if(NOT LLVM_ENABLE_RTTI)
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fno-rtti")
endif()

set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -O1")

# ===============================================================================
# 3. ADD THE TARGET
# ===============================================================================
add_library(Cpp2C SHARED
  AnnotationPrinter/AnnotationPrinterConsumer.cc
  AnnotationRemover/AnnotationRemoverConsumer.cc
  Deduplicator/DeduplicatorConsumer.cc
  Callbacks/ForestCollector.cc
  Callbacks/MacroNameCollector.cc
  Cpp2C.cc
  Cpp2C/Cpp2CAction.cc

  # This should probably have a better name or be moved...
  CppSig/CppSigUtils.cc
  CppSig/MacroArgument.cc
  CppSig/MacroExpansionNode.cc
  CppSig/MacroForest.cc
  Transformer/Properties.cc
  Transformer/TransformedDefinition.cc
  Transformer/TransformerConsumer.cc
  Utils/ExpansionUtils.cc
  Utils/Logging/TransformerMessages.cc
  Utils/SourceRangeCollection.cc
  Utils/TransformedDeclarationAnnotation.cc
  Visitors/CollectCpp2CAnnotatedDeclsVisitor.cc
  Visitors/CollectDeclNamesVisitor.cc
  Visitors/DeanonymizerVisitor.cc
  Visitors/DeclRefExprAndCallExprDDVisitor
  Visitors/ForwardDeclDDVisitor.cc
  Visitors/FunctionDefinitionDDVisitor.cc
  Visitors/MacroTransformationMapperVisitor.cc
)

target_include_directories(Cpp2C PUBLIC "${PROJECT_SOURCE_DIR}/include")

# Allow undefined symbols in shared objects on Darwin (this is the default
# behaviour on Linux)
target_link_libraries(Cpp2C
  "$<$<PLATFORM_ID:Darwin>:-undefined dynamic_lookup>")
