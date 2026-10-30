module Compiler.ScopeAndNameResolution.Data

import Frontend.ASTData
import Frontend.ASTPhases
import Frontend.Helper
import Frontend.QuantumAnnotations
import Frontend.Source
import Frontend.Syntax.AST
import Compiler.Type

import Data.SortedMap

%default total

public export
ResolvedSymbolInfo : Type
ResolvedSymbolInfo = SymbolInfo ()

public export
data VariableMutability
  = ImmutableVariable
  | MutableVariable

public export
record LocalVariableInfo (storage: Type) where
  constructor MkLocalVariableInfo
  mutability     : VariableMutability
  quantumStorage : storage

public export
ResolvedLocalVariableInfo : Type
ResolvedLocalVariableInfo = LocalVariableInfo ()

public export
record ScopeTables where
  constructor MkScopeTables
  currentScope     : ScopeId                                       -- this field reflects the current scope while ScopeTables are being threaded through code using a State monad
  currentScopeKind : ScopeKind
  currentModule    : SymbolId                                      -- the module enclosing the current scope; threaded like currentScope
  constContextBoundary : Maybe ScopeId                             -- scope enclosing innermost array length or repeat count where a name cannot be a local parameter
  nodeScopes       : SortedMap NodeId ScopeId                      -- lexical environment used to resolve a node
  symbols          : SortedMap SymbolId ResolvedSymbolInfo
  localVariables   : SortedMap SymbolId ResolvedLocalVariableInfo  -- Local/parameter declaration metadata, keyed by the corresponding SymbolId.
  references       : SortedMap SymbolId (SnocList SymbolReference)
  scopes           : SortedMap ScopeId ScopeInfo
  memberScopes     : SortedMap SymbolId ScopeId                    -- Given a symbol, which scope contains its members? Member example: const and functions inside a module

public export
(.nextSymbolId) : ScopeTables -> SymbolId
(.nextSymbolId) tables =
  case maxKey tables.symbols of
       Nothing => MkSymbolId 0
       Just (MkSymbolId n) => MkSymbolId (S n)

public export
(.nextScopeId) : ScopeTables-> ScopeId
(.nextScopeId) tables =
  case maxKey tables.scopes of
       Nothing => MkScopeId 0
       Just (MkScopeId n) => MkScopeId (S n)

public export
record ResolvedModule where
  constructor MkResolvedModule
  rootModule     : SymbolId
  rootScope      : ScopeId
  ast            : ResolvedSourceFile
  tables         : ScopeTables

public export
data ResolutionError
  = UnresolvedName String SourceSpan                                    -- No matching declaration is visible at the use site
  | DuplicateDeclaration String (List SymbolId) SourceSpan SourceSpan   -- Current name span, then the previous declaration name span.
                                                                        -- Declarations conflict in the same scope and namespace,
  | InaccessibleSymbol String SymbolId SourceSpan                       -- Declaration exists but visibility rules prohibit access,
                                                                        -- example: accessing a private function from a sibling module.
  | BindingShadowsConstant String SymbolId SourceSpan SourceSpan        -- An explicit mutable binder cannot shadow a visible constant.
                                                                        -- Immutable bare names instead resolve to constant patterns.
  | LocalValueUsedAsConstant String SymbolId SourceSpan SourceSpan      -- Use span, then the local's declaration name span. As in Rust (E0435),
                                                                        -- array lengths and repeat counts cannot use enclosing locals,

-- Guide for future extensions:
-- IllegalCapture String SourceSpan                         -- Nested functions are forbidden from capturing enclosing locals,
                                                             -- example: `fn outer() { let x = 1; fn inner() -> i32 { x } }`
-- IllegalShadowing String SymbolId SourceSpan SourceSpan   -- A declaration shadows a protected name,
-- AmbiguousName String (List SymbolId) SourceSpan          -- Lookup finds multiple candidates without a rule selecting one.
-- UnresolvedPathSegment, when a component of a qualified path cannot be found, example: `my_library::missing::helper`.
-- InvalidPathQualifier, when a resolved symbol cannot qualify another path component, example: `count::helper` where `count` is an integer variable.
-- ConflictingImports, when imports introduce different symbols under the same name where forbidden, example: `use a::helper; use b::helper;`.
-- WrongNamespace, when a name exists only in a namespace incompatible with its use, example: `let y: x = 0;` where `x` names only a variable.
-- UseBeforeDeclaration, optionally when a local variable is referenced before its declaration, example: `let y = x; let x = 1;` with no earlier `x` in scope.
-- ModuleNotFound, during module loading when an external module cannot be located, example: `mod my_library;` with no corresponding module source.
-- CyclicImport, when an import cycle prevents resolution or violates Leaf’s rules, example: `a::helper` re-exports `b::helper`, which re-exports `a::helper`, with no actual definition.

export
showResolutionError : ResolutionError -> String
showResolutionError (UnresolvedName name sourceSpan) =
  "Could not find a matching declaration for this name: '\{name}' in '\{sourceSpan}'."
showResolutionError (DuplicateDeclaration name symbolIds sourceSpan previousSpan) =
  "A duplicate declaration for name: '\{name}' declared in '\{sourceSpan}' was found; the previous declaration is in '\{previousSpan}'."
showResolutionError (InaccessibleSymbol name _ sourceSpan) =
  "At current location '\{sourceSpan}' the name: '\{name}' is not publicly accessible."
showResolutionError (BindingShadowsConstant name _ sourceSpan constantSpan) =
  "The mutable binding for name: '\{name}' in '\{sourceSpan}' cannot shadow the constant declared in '\{constantSpan}'."
showResolutionError (LocalValueUsedAsConstant name _ sourceSpan localSpan) =
  "The local: '\{name}' used in '\{sourceSpan}' is not a constant and cannot be used in an array length or repeat count; it is declared in '\{localSpan}'."

export
implementation Show ResolutionError where
  show = showResolutionError
