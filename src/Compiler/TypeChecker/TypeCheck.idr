module Compiler.TypeChecker.TypeCheck

import Control.Monad.State

import Compiler.ScopeAndNameResolution.Data
import Compiler.TypeChecker.Data
import Compiler.TypeChecker.InitialTypeCheckPass
import Compiler.TypeChecker.SecondTypeCheckPass
import Compiler.TypeChecker.ThirdTypeCheckPass

%default total

public export
typeCheck : ResolvedModule -> Either TypeError TypedModule
typeCheck resolvedModule = do
    signatureTables <- initialTypeCheckPass resolvedModule
    typedModule     <- secondTypeCheckPass resolvedModule signatureTables
    thirdTypeCheckPass typedModule


