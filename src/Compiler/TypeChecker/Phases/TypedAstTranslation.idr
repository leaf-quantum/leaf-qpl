module Compiler.TypeChecker.Phases.TypedAstTranslation

import Compiler.TypeChecker.Data
import Frontend.ASTData
import Frontend.ASTPhases
import Frontend.Syntax.AST

%default total

export
translateSourceFile : TypeTables -> ResolvedSourceFile -> TypedSourceFile
translateSourceFile = ?translateSourceFileH


