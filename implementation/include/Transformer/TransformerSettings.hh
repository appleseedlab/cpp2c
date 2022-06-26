#pragma once

namespace Transformer
{
    struct TransformerSettings
    {
        bool OverwriteFiles = false;
        bool Verbose = false;
        bool OnlyCollectNotDefinedInStdHeaders = true;
        bool TransformConditionalEvaluation = false;
    };
} // namespace Transformer