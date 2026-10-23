module Compiler.TypeChecker.Data

import public Compiler.ScopeAndNameResolution.Data

import Frontend.ASTData
import Frontend.ASTPhases
import Frontend.Source
import Frontend.Syntax.AST
import Frontend.Syntax.Common
import Compiler.Type

import Data.SortedMap

%default total

public export
TypedSymbolInfo : Type
TypedSymbolInfo = SymbolInfo (Maybe LeafType)

public export
record TypeTables where
  constructor MkTypeTables
  currentScope     : ScopeId                                  -- this field reflects the current scope while ScopeTables are being threaded through code using a State monad
  currentScopeKind : ScopeKind
  currentModule    : SymbolId                                 -- the module enclosing the current scope; threaded like currentScope
  constContextBoundary : Maybe ScopeId                        -- scope enclosing innermost array length or repeat count where a name cannot be a local parameter
  nodeScopes       : SortedMap NodeId ScopeId                 -- lexical environment used to resolve a node
  symbols          : SortedMap SymbolId TypedSymbolInfo
  localVariables   : SortedMap SymbolId LocalVariableInfo     -- Local/parameter declaration metadata, keyed by the corresponding SymbolId.
  references       : SortedMap SymbolId (SnocList SymbolReference)
  scopes           : SortedMap ScopeId ScopeInfo
  memberScopes     : SortedMap SymbolId ScopeId               -- Given a symbol, which scope contains its members? Member example: const and functions inside a module
  expressionTypes  : SortedMap NodeId LeafType

public export
record TypedModule where
  constructor MkTypedModule
  rootModule     : SymbolId
  rootScope      : ScopeId
  ast            : TypedSourceFile
  tables         : TypeTables

public export
data TypeError
  = TypeMismatch LeafType LeafType SourceSpan                  -- expected type, actual type
  | CannotInferType SourceSpan                                 -- insufficient information to determine a type
  | NotCallable LeafType SourceSpan                            -- attempted to call a value whose type is not callable
  | WrongArgumentCount Nat Nat SourceSpan                      -- expected count, actual count
  | InvalidUnaryOperand String LeafType SourceSpan             -- operator, operand type
  | InvalidBinaryOperands String LeafType LeafType SourceSpan  -- operator, left type, right type
  | NotIndexable LeafType SourceSpan                           -- attempted indexing on an unsupported type
  | IntegerLiteralOutOfRange Integer LeafType SourceSpan       -- literal value, target type
  | InvalidCast LeafType LeafType SourceSpan                   -- source type, target typei
  | InvalidQuantumQualifier String LeafType SourceSpan         -- qualifier, annotated type, ex: let scratch n: i32 = 5;
  | InvalidQubitReference SourceSpan                           -- explicit 'mut' on a qubit reference, ex: &mut qubit or &mut [qubit]
  | InvalidConditionType String LeafType SourceSpan            -- construct if/qif/sif/etc., actual type, ex: if q { ... } where q: qubit
  | QuantumWidthMismatch String Nat Nat SourceSpan             -- context, expected width, actual width. ex: ctrl(&q0, &q1).on(bs"1").apply(H)(&target);
  | EffectViolation FunctionEffect FunctionEffect SourceSpan   -- enclosing effect restriction, offending operation's effect, ex: measr(&q) inside a unitary function,
  | MissingCapability String SourceSpan                        -- required capability (adjoint or ctrl), ex: adjoint(f) when f has no established adjoint support
  | InvalidQuantumPattern String SourceSpan               -- explanation of the invalid pattern, ex: mixing integer and basis-string patterns in one qmatch, or using _ in smatch.
                                                              -- type cycles?

