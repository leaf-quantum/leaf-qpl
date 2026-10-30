module Compiler.TypeChecker.Data

import Data.List1
import Data.SortedMap

import Compiler.ScopeAndNameResolution.Data
import Compiler.Type
import Frontend.ASTData
import Frontend.ASTPhases
import Frontend.QuantumAnnotations
import Frontend.Source
import Frontend.Syntax.AST
import Frontend.Syntax.Common
import Frontend.Token

%default total

public export
data InferredType
  = TypeNotYetResolved
  | ResolvedType LeafType
  | NoValueType                                              -- the symbol names a namespace or a type, so it has no value type

public export
TypedSymbolInfo : Type
TypedSymbolInfo = SymbolInfo InferredType

public export
data QbitStorageStatus
  = PendingQbitClassification
  | NotQbitLocal
  | AssignedQbitStorage QuantumStorageProperties

public export
TypedLocalVariableInfo : Type
TypedLocalVariableInfo = LocalVariableInfo QbitStorageStatus

public export
data ConstValue
  = ConstInteger Integer
  | ConstFloat Double
  | ConstBool Bool
  | ConstUnit
  | ConstTuple (List1 ConstValue)
  | ConstArray (List ConstValue)

public export
data Coercion
  = FloatToAngle TypPrimName               -- an f32/f64 gate angle argument becomes this angle32/angle64
  | ArrayToSlice Nat                       -- &[T; N] passed as &[T]; N kept so lowering can specialize
  | BitToBool                              -- a bit condition: `if b` means `if b == 1`

public export
data BuiltinForm                           -- which documented overload of a builtin was chosen
  = SingleQbit                            -- measr(q), qalloc(), barrier()
  | SelectedQbits Nat                     -- measr(q1, q2, q3), barrier(q1, q2, q3)
  | QbitArray Nat                         -- measr(qs), qalloc(3)

public export
data Callee
  = FunctionCall SymbolId                  -- declared, prelude or associated function named at the call
  | MethodCall SymbolId                    -- resolved method, including built-in len/rev/tensor
  | ValueCall                              -- a function-typed value: parameter, adjoint(f), ctrl(..).apply(f)
  | BuiltinCall Builtin BuiltinForm

public export
data ArgumentPassing
  = ByValue                                -- copied (classical) or moved (quantum)
  | Threaded                               -- &q, &qs[1..], &mut x, or a qbit reference: the place is updated

public export
record CallResolution where
  constructor MkCallResolution
  callee          : Callee
  argumentPassing : List ArgumentPassing   -- one per argument, in order

public export
record TypeTables where
  constructor MkTypeTables
  scopes           : SortedMap ScopeId ScopeInfo
  nodeScopes       : SortedMap NodeId ScopeId                   -- lexical environment used to resolve a node
  symbols          : SortedMap SymbolId TypedSymbolInfo
  localVariables   : SortedMap SymbolId TypedLocalVariableInfo  -- Local/parameter declaration metadata, keyed by the corresponding SymbolId.
  memberScopes     : SortedMap SymbolId ScopeId                 -- Given a symbol, which scope contains its members? Member example: const and functions inside a module
  references       : SortedMap SymbolId (SnocList SymbolReference)
  constValues      : SortedMap SymbolId ConstValue
  expressionTypes  : SortedMap NodeId LeafType                  -- every Expr node, type before any coercion
  patternTypes     : SortedMap NodeId LeafType                  -- every Pattern node: type of the value it matches
  coercions        : SortedMap NodeId Coercion                  -- Expr nodes whose value is implicitly converted
  calls            : SortedMap NodeId CallResolution            -- every ExprCall / ExprMethodCall node

--------------------------------------------------------------------------------
-- Ownership
--------------------------------------------------------------------------------
-- Filled by the third pass from the typed AST. An access event records what an
-- operation does to a place; whether that is legal, and whether it is the
-- place's last use, is decided by the ownership analysis over control flow.
--------------------------------------------------------------------------------

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

-- What a loop, adjoint or ctrl body touches from outside it. Lowering turns
-- `updated` into letrec parameters and results, or into a unitary's inputs
-- and outputs, and passes `readOnly` in unchanged.
public export
record Footprint where
  constructor MkFootprint
  updated  : List Place
  readOnly : List Place

public export
data CleanupAction
  = ResetScratch SymbolId                 -- `scratch` local: reset at scope exit
  | UncomputeLocal SymbolId               -- `:=` local: uncompute at scope exit

public export
record OwnershipTables where
  constructor MkOwnershipTables
  -- Events directly attributed to an expression/statement, in local evaluation
  -- order; accesses recorded on child nodes must not be duplicated here.
  -- Compile-time-only references (e.g. path qualifiers) produce no access event.
  -- SortedMap key order is NOT execution order.
  accesses       : SortedMap NodeId (List AccessEvent)
  footprints     : SortedMap NodeId Footprint             -- loop / while / for / adjoint { } / ctrl(..) { } nodes
  cleanups       : SortedMap NodeId (List CleanupAction)  -- scope exits: block ends, return, break, continue
  borrowedPlaces : SortedMap SymbolId Place               -- reference locals: `let qv = &qs[1..]` gives qv ↦ qs[1..]

public export
record TypedModule where
  constructor MkTypedModule
  rootModule     : SymbolId
  rootScope      : ScopeId
  ast            : TypedSourceFile
  tables         : TypeTables
  ownership      : OwnershipTables

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
  | InvalidCast LeafType LeafType SourceSpan                   -- source type, target type
  | InvalidQuantumQualifier String LeafType SourceSpan         -- qualifier, annotated type, ex: let scratch n: i32 = 5;
  | InvalidQbitReference SourceSpan                           -- explicit 'mut' on a qbit reference, ex: &mut qbit or &mut [qbit]
  | InvalidConditionType String LeafType SourceSpan            -- construct if/qif/sif/etc., actual type, ex: if q { ... } where q: qbit
  | QuantumWidthMismatch String Nat Nat SourceSpan             -- context, expected width, actual width. ex: ctrl(&q0, &q1).on(bs"1").apply(H)(&target);
  | EffectViolation FunctionEffect FunctionEffect SourceSpan   -- enclosing effect restriction, offending operation's effect, ex: measr(&q) inside a unitary function,
  | MissingCapability String SourceSpan                        -- required capability (adjoint or ctrl), ex: adjoint(f) when f has no established adjoint support
  | InvalidQuantumPattern String SourceSpan               -- explanation of the invalid pattern, ex: mixing integer and basis-string patterns in one qmatch, or using _ in smatch.
                                                              -- type cycles?

export
showTypeError : TypeError -> String
showTypeError typeError =
  case typeError of
    TypeMismatch expected actual sourceSpan =>
      at sourceSpan $ "Expected type '" ++ show expected ++ "', but found '" ++ show actual ++ "'."
    CannotInferType sourceSpan =>
      at sourceSpan "Cannot infer the type; add a type annotation."
    NotCallable actual sourceSpan =>
      at sourceSpan $ "Cannot call a value of type '" ++ show actual ++ "'."
    WrongArgumentCount expected actual sourceSpan =>
      at sourceSpan $ "Expected " ++ show expected ++ " argument(s), but received " ++ show actual ++ "."
    InvalidUnaryOperand operator operandType sourceSpan =>
      at sourceSpan $ "Operator '" ++ operator ++ "' cannot be applied to type '" ++ show operandType ++ "'."
    InvalidBinaryOperands operator leftType rightType sourceSpan =>
      at sourceSpan $ "Operator '" ++ operator ++ "' cannot be applied to types '" ++ show leftType ++ "' and '" ++ show rightType ++ "'."
    NotIndexable actual sourceSpan =>
      at sourceSpan $ "Cannot index a value of type '" ++ show actual ++ "'."
    IntegerLiteralOutOfRange value targetType sourceSpan =>
      at sourceSpan $ "Integer literal " ++ show value ++ " is out of range for type '" ++ show targetType ++ "'."
    InvalidCast sourceType targetType sourceSpan =>
      at sourceSpan $ "Cannot cast type '" ++ show sourceType ++ "' to '" ++ show targetType ++ "'."
    InvalidQuantumQualifier qualifier actual sourceSpan =>
      at sourceSpan $ "Quantum qualifier '" ++ qualifier ++ "' is not valid for type '" ++ show actual ++ "'."
    InvalidQbitReference sourceSpan =>
      at sourceSpan "Qbit references are mutable by default; omit 'mut' from the reference."
    InvalidConditionType construct actual sourceSpan =>
      at sourceSpan $ "Type '" ++ show actual ++ "' is not a valid condition type for '" ++ construct ++ "'."
    QuantumWidthMismatch context expected actual sourceSpan =>
      at sourceSpan $ "Quantum width mismatch in " ++ context ++ ": expected " ++ show expected ++ ", but found " ++ show actual ++ "."
    EffectViolation enclosingEffect operationEffect sourceSpan =>
      at sourceSpan $ "An operation with effect '" ++ show operationEffect ++ "' is not permitted in a function with effect '" ++ show enclosingEffect ++ "'."
    MissingCapability capability sourceSpan =>
      at sourceSpan $ "The callable does not have established support for '" ++ capability ++ "'."
    InvalidQuantumPattern explanation sourceSpan =>
      at sourceSpan $ "Invalid quantum pattern: " ++ explanation
  where
    at : SourceSpan -> String -> String
    at sourceSpan message = "Type error at \{sourceSpan}: \{message}"

public export
implementation Show TypeError where
  show = showTypeError

