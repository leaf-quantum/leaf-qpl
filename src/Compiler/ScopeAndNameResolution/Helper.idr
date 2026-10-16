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
  | InnacessibleBinding SymbolId
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
