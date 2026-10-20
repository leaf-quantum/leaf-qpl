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

-- ReferenceRole describes syntax; AccessKind describes the typed operation on
-- a value. Neither records flow-dependent facts such as whether it was already
-- moved or whether this is its last use; those belong to ownership analysis.
public export
data AccessKind
  = ReadAccess          -- Observe/copy a value without transferring ownership.
  | WriteAccess         -- Initialize or replace a value.
  | MoveAccess          -- Transfer ownership elsewhere.
  | SharedBorrowAccess  -- Borrow without allowing mutation through this borrow.
  | MutableBorrowAccess -- Borrow with permission to mutate through this borrow.
  | ConsumeAccess       -- Consume a resource without transferring it onward.

public export
data PlaceRoot
  = LocalRoot SymbolId   -- A local variable or parameter, including a generated local.
  | TemporaryRoot NodeId -- Temporary storage produced by an expression, such as f() in f().x.

-- Projections are applied from left to right, starting at the place's root.
public export
data PlaceProjection
  = FieldProjection SymbolId -- The resolved field declaration, not its written spelling.
  | TupleProjection Nat      -- A zero-based tuple element index.
  | IndexProjection NodeId   -- The expression computing an array/slice index or range.
  | DereferenceProjection    -- The storage reached through a reference.

-- A field SymbolId alone identifies a declaration, not a particular value's
-- storage. For p.x, retain LocalRoot p and [FieldProjection x].
-- Different index-expression IDs or reference roots do not prove disjointness:
-- ownership analysis must account for dynamic indices and reference aliasing.
public export
record Place where
  constructor MkPlace
  root        : PlaceRoot
  projections : List PlaceProjection

public export
record AccessEvent where
  constructor MkAccessEvent
  kind       : AccessKind -- Classified using types and the operation's semantics.
  place      : Place      -- The affected local, temporary, field, element or referent.
  occurrence : AstInfo    -- The access's AST occurrence and diagnostic source span.

public export
record ScopeAndTypeTables where
  constructor MkScopeAndTypeTables
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
  -- Events directly attributed to an expression/statement, in local evaluation
  -- order; accesses recorded on child nodes must not be duplicated here.
  -- Compile-time-only references (e.g. path qualifiers) produce no access event.
  -- SortedMap key order is NOT execution order: a later control-flow analysis
  -- determines legal moves/borrows, last uses and required cleanup.
  accesses        : SortedMap NodeId (List AccessEvent)

public export
record TypedModule where
  constructor MkTypedModule
  rootModule     : SymbolId
  rootScope      : ScopeId
  ast            : TypedSourceFile
  tables         : ScopeAndTypeTables

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

