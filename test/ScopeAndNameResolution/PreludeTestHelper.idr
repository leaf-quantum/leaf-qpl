module ScopeAndNameResolution.PreludeTestHelper

import Compiler.Prelude
import Compiler.ScopeAndNameResolution.Data
import Frontend.ASTData
import Frontend.ASTPhases
import Frontend.Source
import Frontend.Syntax.AST
import Frontend.Syntax.Name
import ScopeAndNameResolution.Helper

import Data.List
import Data.Maybe
import Data.SnocList
import Data.SortedMap

%default total

isPrelude : SymbolOrigin -> Bool
isPrelude PreludeSymbol = True
isPrelude _ = False

isPublic : SymbolVisibility -> Bool
isPublic PublicVisibility = True
isPublic _ = False

isModuleScope : ScopeKind -> Bool
isModuleScope ModuleScope = True
isModuleScope _ = False

isPreludeModule : ResolvedSymbolInfo -> Bool
isPreludeModule symbol = case symbol.symbolKind of
  SymbolModule => isPrelude symbol.origin
  _ => False

-- Check ownership, lexical ancestry and declaration order independently of
-- the general validator, which deliberately does not require complete tables.
export
preludeLayout : ResolvedModule -> Maybe Bool
preludeLayout resolved = do
  let tables = resolved.tables
  root <- lookup resolved.rootScope tables.scopes
  preludeScopeId <- root.parent
  preludeScope <- lookup preludeScopeId tables.scopes
  [owner] <- pure (filter isPreludeModule (map snd (SortedMap.toList tables.symbols)))
    | _ => Nothing
  let bindings = map snd (SortedMap.toList preludeScope.valueBindings)
  pure $
    tables.currentScope == resolved.rootScope &&
    isModuleScope tables.currentScopeKind &&
    tables.currentModule == resolved.rootModule &&
    isModuleScope root.kind && isModuleScope preludeScope.kind &&
    (case preludeScope.origin of PreludeScope => True; _ => False) &&
    isNothing preludeScope.parent &&
    owner.declaringScope == resolved.rootScope &&
    owner.declaringModule == resolved.rootModule &&
    lookup owner.symbolId tables.memberScopes == Just preludeScopeId &&
    lookup resolved.rootModule tables.memberScopes == Just resolved.rootScope &&
    elem owner.symbolId (root.declaredSymbolsInOrder <>> []) &&
    sort (map (.writtenName) bindings) == sort preludeFunctionNames &&
    sort (preludeScope.declaredSymbolsInOrder <>> []) == sort (map (.target) bindings) &&
    all (validBinding tables preludeScopeId owner.symbolId) bindings
  where
    validBinding : ScopeTables -> ScopeId -> SymbolId -> ScopeBinding -> Bool
    validBinding tables scopeId moduleId binding =
      case lookup binding.target tables.symbols of
        Nothing => False
        Just symbol =>
          (case binding.bindingKind of PreludeBinding => True; _ => False) &&
          isNothing binding.introducedAt && isPublic binding.bindingVisibility &&
          (case symbol.symbolKind of SymbolFunction => True; _ => False) &&
          isPrelude symbol.origin && isPublic symbol.visibility &&
          symbol.symbolId == binding.target && symbol.declaredName == binding.writtenName &&
          symbol.declaringScope == scopeId && symbol.declaringModule == moduleId &&
          isNothing (lookup symbol.symbolId tables.localVariables)

export
useOrigins : String -> Maybe (List (String, String))
useOrigins source = do
  resolved <- resolvedSource source
  traverse (describe resolved.tables) (valueReferences resolved)
  where
    describe : ScopeTables -> SymbolReference -> Maybe (String, String)
    describe tables reference = do
      symbol <- lookup reference.target tables.symbols
      let origin = if isPrelude symbol.origin then "prelude" else
            case symbol.symbolKind of
              SymbolConstant => "other"
              kind => kindText kind
      pure (reference.writtenName, origin)

export
missingName : String -> Maybe String
missingName source = case expectUnresolvedName source of
  Right name => Just name
  Left _ => Nothing

export
constantShadowsPrelude : ResolvedModule -> Maybe Bool
constantShadowsPrelude resolved = do
  MkSourceFileNode _ [MkAstNode _ _ (ItemFunction fn), MkAstNode _ _ (ItemConst con)] <- pure resolved.ast.value
    | _ => Nothing
  MkAstNode _ _ (StatementSemiExpression expression) :: _ <- pure fn.functionBody.value.blockStatements
    | _ => Nothing
  ExprName use <- pure expression.value | _ => Nothing
  root <- lookup resolved.rootScope resolved.tables.scopes
  preludeId <- root.parent
  preludeScope <- lookup preludeId resolved.tables.scopes
  sourceBinding <- lookup "sin" root.valueBindings
  preludeBinding <- lookup "sin" preludeScope.valueBindings
  sourceSymbol <- lookup sourceBinding.target resolved.tables.symbols
  preludeSymbol <- lookup preludeBinding.target resolved.tables.symbols
  bodyScope <- lookup fn.functionBody.astInfo.nodeId resolved.tables.nodeScopes
  [reference] <- pure (valueReferences resolved) | _ => Nothing
  layout <- preludeLayout resolved
  pure (layout && sourceBinding.target /= preludeBinding.target &&
        sourceBinding.target == con.constName.value.resolvedNameNodeSymbolId &&
        use.value.resolvedNameNodeSymbolId == sourceBinding.target &&
        (case sourceBinding.bindingKind of DeclaredBinding => True; _ => False) &&
        (case sourceBinding.bindingVisibility of ModuleVisibility => True; _ => False) &&
        (case sourceSymbol.symbolKind of SymbolConstant => True; _ => False) &&
        (case sourceSymbol.origin of SourceSymbol _ => True; _ => False) &&
        sourceSymbol.declaringScope == resolved.rootScope && sourceSymbol.declaringModule == resolved.rootModule &&
        isPrelude preludeSymbol.origin && preludeSymbol.declaringScope == preludeId &&
        (case preludeBinding.bindingKind of PreludeBinding => True; _ => False) &&
        isPublic preludeBinding.bindingVisibility &&
        reference.target == sourceBinding.target && reference.writtenName == "sin" &&
        reference.occurrence.nodeId == use.astInfo.nodeId &&
        spanKey reference.occurrence.span == spanKey use.astInfo.span &&
        reference.contextNode == expression.astInfo.nodeId && reference.enclosingScope == bodyScope &&
        lookup expression.astInfo.nodeId resolved.tables.nodeScopes == Just bodyScope &&
        lookup use.astInfo.nodeId resolved.tables.nodeScopes == Just bodyScope &&
        isNothing (lookup preludeBinding.target resolved.tables.references) &&
        length (allReferences resolved) == 3)
