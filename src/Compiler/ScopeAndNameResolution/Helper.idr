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
retrieveSymbolBinding symbolName scopeTables = ?xxx
-- get ScopeInfo
-- from ScopeInfo valueBindings retrieve ScopBinding by key provided by symbol text 
