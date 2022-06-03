#include "Cpp2C/Cpp2CAction.hh"

#include "clang/Frontend/FrontendPluginRegistry.h"

using clang::FrontendPluginRegistry;

//-----------------------------------------------------------------------------
// Registration
//-----------------------------------------------------------------------------
// TODO: Add an action with command line arguments for choosing which
// consumer to use
static FrontendPluginRegistry::Add<Cpp2C::Cpp2CAction>
    X("cpp2c", "Transform CPP macros to C functions");
