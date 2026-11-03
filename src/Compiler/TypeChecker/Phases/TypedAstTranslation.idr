module Compiler.TypeChecker.Phases.TypedAstTranslation

import Compiler.TypeChecker.Data
import Frontend.ASTData
import Frontend.ASTPhases
import Frontend.Syntax.AST

%default total

export
translateAst : TypeTables -> ResolvedSourceFile -> TypedSourceFile
translateAst = ?translateSourceFileH


