#include "Utils/Logging/TransformerMessages.hh"
#include "Utils/ExpansionUtils.hh"

namespace Utils
{
    namespace Logging
    {
        using namespace clang;
        using CppSig::MacroExpansionNode;
        using llvm::raw_fd_ostream;
        using std::string;
        using Transformer::TransformedDefinition;

        void emitUntransformedMessage(
            raw_fd_ostream &OS,
            ASTContext &Ctx,
            MacroExpansionNode *Expansion,
            string Category,
            string Reason)
        {
            SourceManager &SM = Ctx.getSourceManager();
            const LangOptions &LO = Ctx.getLangOpts();
            auto ST = Expansion->getStmtsRef().size() > 0 ? *Expansion->getStmtsRef().begin() : nullptr;
            auto ND = Utils::getTopLevelNamedDeclStmtExpandedIn(Ctx, ST);
            OS << "CPP2C:"
               << "Untransformed Expansion,"
               << "\"" << hashMacro(Expansion->getMI(), SM, LO) << "\","
               << Expansion->getSpellingRange().getBegin().printToString(SM) << ","
               << ND->getNameAsString() << ","
               << Category << ","
               << Reason << "\n";
        }

        void emitMacroDefinitionMessage(
            raw_fd_ostream &OS,
            const MacroDirective *MD,
            SourceManager &SM,
            const LangOptions &LO)
        {
            OS << "CPP2C:"
               << "Macro Definition,"
               << '"' << hashMacro(MD->getMacroInfo(), SM, LO) << '"' << ','
               << MD->getMacroInfo()->getDefinitionLoc().printToString(SM) << "\n";
        }

        void emitMacroExpansionMessage(
            raw_fd_ostream &OS,
            SourceRange SpellingRange,
            const MacroDefinition &MD,
            SourceManager &SM,
            const LangOptions &LO)
        {
            SourceLocation SpellingLoc = SpellingRange.getBegin();
            OS << "CPP2C:"
               << "Macro Expansion,"
               << "\"" << hashMacro(MD.getMacroInfo(), SM, LO) << "\","
               << SpellingLoc.printToString(SM) << "\n";
        }

        void emitTransformedDefinitionMessage(
            raw_fd_ostream &OS,
            TransformedDefinition *TD,
            ASTContext &Ctx,
            SourceManager &SM,
            const LangOptions &LO)
        {
            string TransformedSignatureNoName =
                TD->getExpansionSignatureOrDeclaration(Ctx, false);
            OS << "CPP2C:"
               << "Transformed Definition,"
               << "\"" << hashMacro(TD->getExpansion()->getMI(), SM, LO) << "\","
               << "\"" << TransformedSignatureNoName << "\""
               << ","
               << TD->getEmittedName() << "\n";
        }

        void emitTransformedExpansionMessage(
            raw_fd_ostream &OS,
            MacroExpansionNode *Expansion,
            ASTContext &Ctx,
            SourceManager &SM,
            const LangOptions &LO)
        {
            auto ND = Utils::getTopLevelNamedDeclStmtExpandedIn(Ctx, *Expansion->getStmtsRef().begin());
            OS << "CPP2C:"
               << "Transformed Expansion,"
               << "\"" << hashMacro(Expansion->getMI(), SM, LO) << "\","
               << Expansion->getSpellingRange().getBegin().printToString(SM) << ","
               << ND->getNameAsString() << "\n";
        }

    } // namespace Logging

} // namespace Utils
