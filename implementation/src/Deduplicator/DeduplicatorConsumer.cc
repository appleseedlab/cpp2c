#include "Deduplicator/DeduplicatorConsumer.hh"
#include "Deduplicator/DeduplicatorConstants.hh"
#include "Visitors/CollectCpp2CAnnotatedDeclsVisitor.hh"
#include "Visitors/CollectReferencingDREs.hh"
#include "Utils/ExpansionUtils.hh"
#include "Utils/TransformedDeclarationAnnotation.hh"

#include "clang/AST/ASTContext.h"
#include "clang/Rewrite/Core/Rewriter.h"
#include "clang/Basic/SourceManager.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/ASTMatchers/ASTMatchers.h"

#include "clang/Lex/Lexer.h"

#include <algorithm>

namespace Deduplicator
{

    DeduplicatorConsumer::DeduplicatorConsumer(DeduplicatorSettings DDSettings)
        : DDSettings(DDSettings) {}

    void DeduplicatorConsumer::debugMsg(std::string msg)
    {
        if (DDSettings.Verbose)
        {
            llvm::errs() << msg;
        }
    }

    void DeduplicatorConsumer::HandleTranslationUnit(clang::ASTContext &Ctx)
    {
        auto &SM = Ctx.getSourceManager();

        auto &LO = Ctx.getLangOpts();
        auto RW = clang::Rewriter(SM, LO);
        auto TUD = Ctx.getTranslationUnitDecl();

        // Get all CPP2C annotated decls in the program
        auto CCADV = Visitors::CollectCpp2CAnnotatedDeclsVisitor(Ctx);
        CCADV.TraverseTranslationUnitDecl(TUD);
        auto AnnotatedDecls = CCADV.getDeclsRef();

        // Deduplicate struct/union/enum forward declarations (TagDecls)
        for (auto &&D : AnnotatedDecls)
        {
            if (auto TD = clang::dyn_cast<clang::TagDecl>(D))
            {
                // Only remove decls that are previously declared in the same file
                // and not definitions
                if ((!TD->isThisDeclarationADefinition()) &&
                    !TD->isFirstDecl() &&
                    (SM.getFileID(D->getBeginLoc()) == SM.getFileID(D->getPreviousDecl()->getBeginLoc())))
                {
                    clang::SourceRange Range(
                        SM.getFileLoc(D->getBeginLoc()),
                        SM.getFileLoc(D->getEndLoc()));
                    Range.setEnd(clang::Lexer::getLocForEndOfToken(Range.getEnd(), 0, SM, LO).getLocWithOffset(1));

                    bool failed = RW.RemoveText(Range);
                    assert(!failed);
                }
            }
        }

        // Remove the decl's old annotations
        // (decl expansion range doesn't include this)
        auto remove_annotations = [&SM, &RW](clang::Decl *D, bool removeSemicolon)
        {
            for (auto &&it : D->attrs())
            {
                clang::SourceRange RemovalRange(
                    SM.getFileLoc(it->getLocation()),
                    SM.getFileLoc(it->getRange().getEnd()));
                std::string prefix = "__attribute__((";
                std::string suffix = removeSemicolon ? "));" : "))";
                int prefixLen = prefix.length();
                int suffixLen = suffix.length();
                RemovalRange.setBegin(RemovalRange.getBegin().getLocWithOffset(-prefixLen));
                RemovalRange.setEnd(RemovalRange.getEnd().getLocWithOffset(suffixLen));
                auto failed = RW.RemoveText(RemovalRange);
                assert(!failed);
            }
        };

        // Remove tag decls from consideration since they've been deduped
        {
            AnnotatedDecls.erase(
                std::remove_if(
                    AnnotatedDecls.begin(),
                    AnnotatedDecls.end(),
                    [](clang::NamedDecl *D)
                    { return llvm::isa_and_nonnull<clang::TagDecl>(D); }),
                AnnotatedDecls.end());
        }

        auto isDefOrInit = [](clang::NamedDecl *D)
        {
            if (auto FD = clang::dyn_cast<clang::FunctionDecl>(D))
            {
                return FD->getDefinition() == FD || FD->isThisDeclarationADefinition();
            }
            else if (auto VD = clang::dyn_cast<clang::VarDecl>(D))
            {
                return VD->getInitializingDeclaration() == D;
            }
            else
            {
                return false;
            }
        };

        // Remove function definitions and var inits so we can
        // be sure that we are only looking at decls
        {
            AnnotatedDecls.erase(
                std::remove_if(
                    AnnotatedDecls.begin(),
                    AnnotatedDecls.end(),
                    isDefOrInit),
                AnnotatedDecls.end());
        }

        // Map each transformed macro to a vector of its transformed declarations
        std::map<std::string, std::vector<clang::NamedDecl *>> MacroHashToTransformedDecls;
        std::map<clang::NamedDecl *, std::string> TransformedDeclToMacroHash;
        std::map<clang::NamedDecl *, std::string> TransformedDeclToTDAHash;
        std::map<clang::NamedDecl *, nlohmann::json> DeclToJSON;
        for (auto &&D : AnnotatedDecls)
        {
            // Get this decl's first annotation
            std::string annotation = Utils::getFirstAnnotationOrEmpty(D);
            nlohmann::json j = Utils::annotationStringToJson(annotation);

            // Create the unique macro hash based on data in
            // the JSON object
            Utils::TransformedDeclarationAnnotation TDA;
            Utils::from_json(j, TDA);
            std::string MacroHash = Utils::hashTDAOriginalMacro(TDA);
            std::string TDAHash = Utils::hashTDA(TDA);

            // Add it to the list of transformed declarations for
            // this macro
            MacroHashToTransformedDecls[MacroHash].push_back(D);
            // Map this transformed decl to its macro hash
            TransformedDeclToMacroHash[D] = MacroHash;
            // Map this transformed decl to its TDA hash
            TransformedDeclToTDAHash[D] = TDAHash;
            // Map this transformed decl to its JSON annotation
            DeclToJSON[D] = j;
        }

        // Keep a set of names of decls to keep
        std::set<std::string> KeptDeclNames;
        // A TDA hash records the original macro a transformed decl came from,
        // where the TD is defined, and the TD's type.
        // We use this to check if we've seen a decl with the same signature before,
        // and to map this this hash to the name of the version to keep
        std::map<std::string, clang::NamedDecl *> TDAHashToKeptDecl;
        auto keepDecl = [this,
                         &KeptDeclNames,
                         &TransformedDeclToTDAHash,
                         &TDAHashToKeptDecl,
                         &DeclToJSON](clang::NamedDecl *D)
        {
            KeptDeclNames.insert(D->getName().str());
            std::string TDAHash = TransformedDeclToTDAHash.at(D);
            this->debugMsg("Inserting hash " + TDAHash + " into TDAHashToKeptDecl\n");
            TDAHashToKeptDecl[TDAHash] = D;
            DeclToJSON.at(D)[Keys::KEEP_ACROSS_RUNS] = true;
        };

        // First check for decls kept in a prior run,
        // because then we don't want to remove them
        for (auto &&D : AnnotatedDecls)
        {
            std::string TDAHash = TransformedDeclToTDAHash[D];

            assert(!isDefOrInit(D));

            if (DeclToJSON.at(D).contains(Keys::KEEP_ACROSS_RUNS))
            {
                keepDecl(D);
            }
        }

        // Next check for decls we haven't seen a TDA hash for yet
        for (auto &&D : AnnotatedDecls)
        {
            std::string TDAHash = TransformedDeclToTDAHash[D];

            // If we haven't seen a decl with this TDA hash yet, then mark
            // this one as the version of this decl to replace other versions of it with
            if (TDAHashToKeptDecl.find(TDAHash) == TDAHashToKeptDecl.end())
            {
                debugMsg("Keeping this decl because a hash for it was not found " + D->getName().str() + "\n");
                keepDecl(D);
            }
        }

        // Debug printing loops
        {
            for (auto &&s : KeptDeclNames)
            {
                debugMsg("Keeping decl " + s + "\n");
            }
            for (auto &&it : TDAHashToKeptDecl)
            {
                debugMsg(it.first + "->" + it.second->getName().str() + "\n");
            }
        }

        // TODO: There is a problem with how we are removing
        // variable definitions (i.e., initializing declarations)

        // Remove all noncanonical transformed definitions
        std::set<clang::NamedDecl *> RemovedDecls;
        std::set<clang::NamedDecl *> RemovedDefs;
        for (auto &&D : AnnotatedDecls)
        {
            auto DeclName = D->getName().str();
            llvm::errs() << "Considering: " << DeclName << " for removal\n";
            // Check if this decl is in the set of decls to keep
            if (KeptDeclNames.find(DeclName) == KeptDeclNames.end())
            {
                debugMsg("Could not find decl " + D->getName().str() + " in set of kept decls, so removing it\n");

                // Remove the decl's annotations
                remove_annotations(D, true);

                // Remove the decl
                clang::SourceRange DeclRange(
                    SM.getFileLoc(D->getBeginLoc()),
                    SM.getFileLoc(D->getEndLoc()));
                DeclRange.setEnd(DeclRange.getEnd().getLocWithOffset(1));
                debugMsg("Decl file loc range: " + DeclRange.printToString(SM));
                bool failed = RW.RemoveText(DeclRange);
                assert(!failed);
                RemovedDecls.insert(D);
                debugMsg("Removed decl" + D->getName().str() + "\n");

                // If this decl has a definition, then remove it as well
                clang::NamedDecl *Def = nullptr;
                bool isVar = false;
                const clang::Expr *InitExpr = nullptr;
                if (auto FD = clang::dyn_cast<clang::FunctionDecl>(D))
                {
                    Def = FD->getDefinition();
                }
                else if (auto VD = clang::dyn_cast<clang::VarDecl>(D))
                {
                    isVar = true;
                    Def = VD->getInitializingDeclaration();
                    InitExpr = VD->getAnyInitializer();
                }
                else
                {
                    assert(false && "Found a transformed decl that was not a function decl OR a var decl\n?");
                }
                assert(D != Def);
                if (nullptr != Def)
                {
                    clang::SourceRange DefRange(
                        SM.getFileLoc(Def->getBeginLoc()),
                        SM.getFileLoc(Def->getEndLoc()));
                    debugMsg("Def range with file locs: " + DefRange.printToString(SM));
                    // TODO: We should be able to remove var decl defs!
                    // For some reason though, they don't always get removed right
                    // if their initializers contain macro invocations.
                    // It's like the macros are fighting back...
                    if (isVar)
                    {
                        // Sometimes, Clang will return the decl's decl instead of its definition
                        // If we try to remove this, the code will crash, since we already
                        // removed the decl.
                        // There may be a way to fix this, but for now we can just check if
                        // the initializer is null, and if so, then just not transform this var decl
                        if (InitExpr == nullptr)
                        {
                            debugMsg("Not removing def of " + D->getName().str() + " because its init is null\n");
                        }
                        else
                        {
                            DefRange.setEnd(clang::Lexer::getAsCharRange(InitExpr->getSourceRange(), SM, LO).getEnd().getLocWithOffset(1));
                        }
                    }
                    DefRange.dump(SM);
                    bool failed = RW.RemoveText(DefRange);
                    assert(!failed);
                    RemovedDefs.insert(Def);
                    debugMsg("Removed def " + Def->getName().str() + "\n");
                }
            }
        }

        // Replace DeclRefExprs to removed decls/defs with their kept counterparts
        {
            std::set<clang::NamedDecl *> RemovedDeclsAndDefs;
            std::set_union(
                RemovedDecls.begin(), RemovedDecls.end(),
                RemovedDefs.begin(), RemovedDefs.end(),
                std::inserter(RemovedDeclsAndDefs, RemovedDeclsAndDefs.begin()));

            Visitors::CollectReferencingDREs Collector(RemovedDeclsAndDefs);
            Collector.TraverseTranslationUnitDecl(TUD);

            auto &DREs = Collector.getDREsRef();
            for (auto &&DRE : DREs)
            {
                auto EnclosingDef = Utils::getTopLevelNamedDeclStmtExpandedIn(Ctx, clang::dyn_cast<clang::Stmt>(DRE));
                // Don't replace dres inside removed defs
                if (RemovedDefs.find(const_cast<clang::NamedDecl *>(EnclosingDef)) !=
                    RemovedDefs.end())
                {
                    debugMsg("Not removing " + DRE->getNameInfo().getAsString() + " because it is inside a removed def\n");
                    continue;
                }

                auto ReferencedDecl = DRE->getFoundDecl();
                // If we found the definition, get the decl instead
                if (isDefOrInit(ReferencedDecl))
                {
                    ReferencedDecl = clang::dyn_cast<clang::NamedDecl>(ReferencedDecl->getPreviousDecl());
                    assert(nullptr != ReferencedDecl);
                }
                assert(DeclToJSON.find(ReferencedDecl) != DeclToJSON.end());

                // Replace this decl with its kept counterpart
                auto ReferencedDeclTDAHash = TransformedDeclToTDAHash[ReferencedDecl];
                auto KeptCounterpart = TDAHashToKeptDecl.at(ReferencedDeclTDAHash);
                auto DREBegin = SM.getFileLoc(DRE->getBeginLoc());
                auto DRENameLen = ReferencedDecl->getName().size();
                bool failed = RW.ReplaceText(DREBegin, DRENameLen, KeptCounterpart->getName());
                assert(!failed);
                debugMsg("Replacing " + ReferencedDecl->getName().str() + " with " + KeptCounterpart->getName().str() + " inside " + EnclosingDef->getName().str() + "\n");
            }
        }

        // Update all kept decls' JSON annotations
        {
            // Write changes to kept decls
            for (auto &&it : TDAHashToKeptDecl)
            {
                auto D = it.second;
                auto j = DeclToJSON.at(D);
                auto newAnnotationString = Utils::escape_json(j.dump());

                // Remove the decl's old annotation
                remove_annotations(D, false);

                // Replace the entire decl with a newly annotated version
                clang::SourceRange ReplacementRange(
                    SM.getFileLoc(D->getBeginLoc()),
                    SM.getFileLoc(D->getEndLoc()));
                // Drop old the decl and add the new one
                D->dropAttrs();
                auto Atty = clang::AnnotateAttr::Create(Ctx, newAnnotationString);
                D->addAttr(Atty);

                // Print the new decl to a string
                std::string S;
                llvm::raw_string_ostream SS(S);
                D->print(SS);

                // Replace the old decl with the new one
                auto failed = RW.ReplaceText(ReplacementRange, SS.str());
                assert(!failed);
            }
        }

        // Rewrite changes, or print them to stdout
        if (DDSettings.OverwriteFiles)
        {
            RW.overwriteChangedFiles();
        }
        else
        {
            // Print the results of the rewriting for the current file
            if (auto RewriteBuf = RW.getRewriteBufferFor(SM.getMainFileID()))
            {
                RewriteBuf->write(llvm::outs());
            }
            else
            {
                debugMsg("No changes\n");
            }
        }
    }
} // namespace Deduplicator
