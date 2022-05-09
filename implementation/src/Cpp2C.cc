#include "Transformer/TransformerAction.hh"

#include "clang/Frontend/FrontendPluginRegistry.h"

using clang::FrontendPluginRegistry;

//-----------------------------------------------------------------------------
// Registration
//-----------------------------------------------------------------------------
// TODO: Add an action with command line arguments for choosing which
// consumer to use
static FrontendPluginRegistry::Add<Transformer::TransformerAction>
    X("cpp2c", "Transform CPP macros to C functions");
