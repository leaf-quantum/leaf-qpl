module Compiler.TypeChecker.Phases.EffectsCheck

import Compiler.TypeChecker.Data
import Frontend.Syntax.AST

%default total

export
checkEffects : TypeTables -> TypedSourceFile -> Either TypeError ()


