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

        std::string hashMacro(
            const std::string MacroName,
            std::size_t DefinitionNumber,
            const clang::MacroInfo *MI,
            clang::SourceManager &SM)
        {
            auto MacroType = MI->isObjectLike() ? "object-like" : "function-like";
            std::string DefinitionFileRealPath =
                Utils::fileRealPathOrEmpty(SM, SM.getFileLoc(MI->getDefinitionLoc()));
            return MacroName + ';' + MacroType + ';' + DefinitionFileRealPath + ';' + std::to_string(DefinitionNumber);
        }

        void emitUntransformedMessage(
            raw_fd_ostream &OS,
            ASTContext &Ctx,
            MacroExpansionNode *Expansion,
            string Category,
            string Reason)
        {
            SourceManager &SM = Ctx.getSourceManager();

            OS << "CPP2C:"
               << "Untransformed Expansion,"
               << hashMacro(Expansion->getName(), Expansion->getDefinitionNumber(), Expansion->getMI(), SM) << ","
               << Expansion->getSpellingRange().getBegin().printToString(SM)
               << Reason << "\n";
        }

        void emitMacroDefinitionMessage(
            raw_fd_ostream &OS,
            const std::string MacroName,
            const MacroDirective *MD,
            SourceManager &SM,
            const LangOptions &LO)
        {
            OS << "CPP2C:"
               << "Macro Definition,"
               << hashMacro(MacroName, Utils::countMacroDefinitions(SM, *MD), MD->getMacroInfo(), SM) << ','
               << MD->getMacroInfo()->getDefinitionLoc().printToString(SM) << "\n";
        }

        void emitMacroExpansionMessage(
            raw_fd_ostream &OS,
            const std::string MacroName,
            SourceRange SpellingRange,
            const MacroDefinition &MD,
            SourceManager &SM,
            const LangOptions &LO)
        {
            SourceLocation SpellingLoc = SpellingRange.getBegin();
            OS << "CPP2C:"
               << "Macro Expansion,"
               << hashMacro(MacroName, Utils::countMacroDefinitions(SM, MD), MD.getMacroInfo(), SM) << ","
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
               << hashMacro(TD->getExpansion()->getName(), TD->getExpansion()->getDefinitionNumber(), TD->getExpansion()->getMI(), SM) << ","
               << TransformedSignatureNoName << ","
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
               << hashMacro(Expansion->getName(), Expansion->getDefinitionNumber(), Expansion->getMI(), SM) << ","
               << Expansion->getSpellingRange().getBegin().printToString(SM) << ","
               << ND->getNameAsString() << "\n";
        }

    } // namespace Logging

} // namespace Utils
