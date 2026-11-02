module Compiler.TypeChecker.TypeCheck

import Control.Monad.State

import Compiler.ScopeAndNameResolution.Data
import Compiler.TypeChecker.BodyCheck
import Compiler.TypeChecker.Data
import Compiler.TypeChecker.OwnershipCheck
import Compiler.TypeChecker.SignatureCheck

%default total

public export
typeCheck : ResolvedModule -> Either TypeError TypedModule
typeCheck resolvedModule = do
    signatureTables <- checkSignatures resolvedModule
    typedModule     <- checkBodies resolvedModule signatureTables
    checkOwnership typedModule


