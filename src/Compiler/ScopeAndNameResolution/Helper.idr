module Compiler.ScopeAndNameResolution.Helper

import Control.Monad.State
import Compiler.ScopeAndNameResolution.Data
import Data.SortedMap
import Frontend.ASTData
import Frontend.ASTPhases
import Frontend.Syntax.Common

%default total

export
recordNodeScope : NodeId -> StateT ScopeTables (Either ResolutionError) ()
recordNodeScope nodeId = modify $ \tables =>
  { nodeScopes := insert nodeId tables.currentScope tables.nodeScopes } tables

export
symbolVisibility : Maybe (AstNode CanonicalAstPhase VisibilityQualifier) -> SymbolVisibility
symbolVisibility (Just (MkAstNode _ _ VisibilityPublic)) = PublicVisibility
symbolVisibility Nothing = ModuleVisibility

public export
data BindingRetrievalResult
  = UnresolvedBinding
  | InaccessibleBinding SymbolId
  | Binding ScopeBinding

export
retrieveSymbolBinding : String -> ScopeTables -> BindingRetrievalResult
retrieveSymbolBinding symbolName tables =
  search (length (SortedMap.toList tables.scopes)) tables.currentScope
  where
    search : Nat -> ScopeId -> BindingRetrievalResult
    search Z _ = UnresolvedBinding
    search (S remaining) scopeId =
      case lookup scopeId tables.scopes of
        Nothing => UnresolvedBinding
        Just scope =>
          case lookup symbolName scope.valueBindings of
            Just binding => Binding binding
            Nothing =>
              case scope.parent of
                Nothing => UnresolvedBinding
                Just parentId => search remaining parentId

export
isLocalSymbolKind : SymbolKind -> Bool
isLocalSymbolKind SymbolLocalBinding = True
isLocalSymbolKind SymbolFunctionParameter = True
isLocalSymbolKind SymbolSelfReceiverParameter = True
isLocalSymbolKind _ = False

||| True when `candidate` is `start` or one of its parent scopes.
export
isScopeOrAncestor : ScopeId -> ScopeId -> ScopeTables -> Bool
isScopeOrAncestor candidate start tables =
  walk (length (SortedMap.toList tables.scopes)) start
  where
    walk : Nat -> ScopeId -> Bool
    walk Z _ = False
    walk (S remaining) scopeId =
      scopeId == candidate ||
        case lookup scopeId tables.scopes >>= (.parent) of
          Nothing => False
          Just parentId => walk remaining parentId

||| Crash on a language feature that scope and name resolution does not support yet.
export
notImplemented : (function : String) -> (feature : String) -> a
notImplemented function feature =
  assert_total $ idris_crash $
    "Scope and name resolution, " ++ function ++ ": not yet implemented: " ++ feature ++ "."

||| Crash on a violated internal invariant: a compiler bug, not invalid Leaf source.
export
unreachable : (function : String) -> (reason : String) -> a
unreachable function reason =
  assert_total $ idris_crash $
    "Scope and name resolution, " ++ function ++ ": internal error: " ++ reason ++ "."
