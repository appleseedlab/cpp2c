#pragma once

namespace Transformer
{
    struct TransformerSettings
    {
        bool OverwriteFiles = false;
        bool Verbose = false;
        bool UnifyMacrosWithSameSignature = false;
        bool OnlyCollectNotDefinedInStdHeaders = true;
    };
} // namespace Transformer