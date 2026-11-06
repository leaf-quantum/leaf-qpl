module Compiler.TypeChecker.Data

import Data.List1
import Data.SortedMap
import Data.String

import Compiler.ScopeAndNameResolution.Data
import Compiler.TypeChecker.Type
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
TypedLocalVarQualifiers : Type
TypedLocalVarQualifiers = LocalVarQualifiers QbitStorageStatus

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
  = SingleQbit                             -- measr(q), qalloc(), barrier()
  | SelectedQbits Nat                      -- measr(q1, q2, q3), barrier(q1, q2, q3)
  | QbitArray Nat                          -- measr(qs), qalloc(3)

public export
data Callee
  = FunctionCall SymbolId                  -- declared, prelude or associated function named at the call
  | MethodCall SymbolId                    -- resolved method, including built-in tensor
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
  -- Scope structure and lexical environments.
  scopes           : SortedMap ScopeId ScopeInfo
  nodeScopes       : SortedMap NodeId ScopeId                       -- lexical environment used to resolve a node
  -- Symbols, declaration metadata, and uses.
  symbols          : SortedMap SymbolId TypedSymbolInfo
  localVarsMeta    : SortedMap SymbolId TypedLocalVarQualifiers     -- Local/parameter declaration metadata, keyed by the corresponding SymbolId.
  memberScopes     : SortedMap SymbolId ScopeId                     -- Given a symbol, which scope contains its members? Member example: const and functions inside a module
  references       : SortedMap SymbolId (SnocList SymbolReference)  -- records where each symbol appears in the program
  -- Evaluated constant values.
  constValues      : SortedMap SymbolId ConstValue
  -- Types assigned to expression and pattern nodes.
  expressionTypes  : SortedMap NodeId LeafType                      -- every Expr node, type before any coercion
  patternTypes     : SortedMap NodeId LeafType                      -- patterns describe how to match or unpack a value and bind names to its parts.
  -- Typing decisions used by later compiler stages.
  coercions        : SortedMap NodeId Coercion                      -- Expr nodes whose value is implicitly converted
  calls            : SortedMap NodeId CallResolution                -- every ExprCall / ExprMethodCall node

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
  | CyclicDeclaration (List String) SourceSpan                 -- symbols involved in a declaration dependency cycle
  -- Constant evaluation
  | NotAConstantExpression SourceSpan                          -- non-const or indirect call, for loop or quantum operation in a const context
  | InvalidArrayLength LeafType SourceSpan                     -- type of a length, repeat count or qalloc count that is not unsigned
  | ArrayLengthTooLarge Integer SourceSpan                     -- length, repeat count or qalloc count of 2^32 or more
  | ArithmeticOverflow LeafType SourceSpan                     -- type of the overflowing operation, ex: 255u8 + 1 or 1u8 << 8
  | DivisionByZeroInConstant SourceSpan
  | ConstEvaluationLimitExceeded SourceSpan                    -- constant evaluation ran out of steps
  | InvalidConstantControlFlow String SourceSpan               -- jump keyword leaving a constant expression, ex: [0; { break; 3 }]
  -- Expressions, patterns and places
  | UnknownMember String SourceSpan                            -- member name; no supported type has named fields or methods
  | InvalidBuiltinContext String SourceSpan                    -- builtin used outside a call or a valid position, ex: let m = measr;
  | UnsupportedFeature String SourceSpan                       -- excluded construct, ex: qstate, tensor, a string literal outside Param
  | IndexOutOfBounds Integer Nat SourceSpan                    -- index, length
  | UnsizedValue LeafType SourceSpan                           -- unsized type used by value, ex: let s = a[1..3];
  | MissingRangeEndpoint String SourceSpan                     -- construct needing the endpoint (rev or for), ex: rev(1..)
  | ReversedRange Integer Integer SourceSpan                   -- start, end, ex: &a[3..1]
  | WrongPatternArity Nat Nat SourceSpan                       -- value's element count, pattern's element count
  | RefutableBindingPattern SourceSpan                         -- ex: let ZERO = 0; where ZERO is a constant
  | MultiplicityMismatch QuantumMultiplicityQualifier QuantumMultiplicityQualifier SourceSpan  -- required, actual, ex: let affine r = H(q); with q linear
  | BreakValueInUnitLoop SourceSpan                            -- break with a value inside while or for
  | AssignmentThroughSharedReference SourceSpan                -- ex: r[0] = 0; where r: &[i32]
  -- Effects and attributes
  | InvalidAttributeEffect String FunctionEffect SourceSpan    -- attribute, function effect, ex: #[qasm_gate] general fn
  | JumpOutOfQuantumBlock String SourceSpan                    -- jump keyword leaving a ctrl or adjoint block
  -- Ownership, initialization and cleanup
  | LinearQbitNotConsumed SourceSpan                           -- binding or temporary holding a linear qbit that is never consumed
  | UseAfterMove String SourceSpan                             -- local used after it was moved
  | UntrackedElementMove SourceSpan                            -- move out of an array through a dynamic index
  | MoveOutOfBorrow SourceSpan                                 -- move of an owned qbit out through a reference
  | OverlappingBorrow SourceSpan                               -- access conflicting with a live exclusive loan
  | MutableBorrowOfImmutable String SourceSpan                 -- local borrowed with &mut but not declared mut
  | ImmutableAssignment String SourceSpan                      -- local written again without mut
  | UninitializedPlace String SourceSpan                       -- local read before it is definitely initialized
  | EscapingReference SourceSpan                               -- reference that outlives its referent
  | UnprovableCleanup SourceSpan                               -- scratch, := or uncompute without a valid inverse and release
  | UnprovableTransformation String SourceSpan                 -- adjoint or ctrl region that cannot be transformed

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
    CyclicDeclaration symbols sourceSpan =>
      at sourceSpan $ "Cyclic declaration dependency involving symbols " ++ (joinBy ", " $ map (\s => "'" ++ s ++ "'") symbols) ++ "."
    NotAConstantExpression sourceSpan =>
      at sourceSpan "This expression cannot be evaluated at compile time."
    InvalidArrayLength actual sourceSpan =>
      at sourceSpan $ "An array length, repeat count or qubit count must have an unsigned integer type, but has type '" ++ show actual ++ "'."
    ArrayLengthTooLarge value sourceSpan =>
      at sourceSpan $ "The length " ++ show value ++ " does not fit in 'u32'."
    ArithmeticOverflow operationType sourceSpan =>
      at sourceSpan $ "Arithmetic overflow in a constant of type '" ++ show operationType ++ "'."
    DivisionByZeroInConstant sourceSpan =>
      at sourceSpan "Division by zero in a constant expression."
    ConstEvaluationLimitExceeded sourceSpan =>
      at sourceSpan "Constant evaluation exceeded its step limit."
    InvalidConstantControlFlow jump sourceSpan =>
      at sourceSpan $ "'" ++ jump ++ "' cannot leave a constant expression."
    UnknownMember member sourceSpan =>
      at sourceSpan $ "No member '" ++ member ++ "' exists on this value."
    InvalidBuiltinContext builtin sourceSpan =>
      at sourceSpan $ "The builtin '" ++ builtin ++ "' cannot be used here."
    UnsupportedFeature feature sourceSpan =>
      at sourceSpan $ "'" ++ feature ++ "' is not supported."
    IndexOutOfBounds index size sourceSpan =>
      at sourceSpan $ "Index " ++ show index ++ " is out of bounds for length " ++ show size ++ "."
    UnsizedValue actual sourceSpan =>
      at sourceSpan $ "A value of unsized type '" ++ show actual ++ "' must be used through a reference."
    MissingRangeEndpoint construct sourceSpan =>
      at sourceSpan $ "The range is missing an endpoint that '" ++ construct ++ "' needs."
    ReversedRange start end sourceSpan =>
      at sourceSpan $ "The range " ++ show start ++ ".." ++ show end ++ " runs backwards."
    WrongPatternArity expected actual sourceSpan =>
      at sourceSpan $ "The value has " ++ show expected ++ " element(s), but the pattern has " ++ show actual ++ "."
    RefutableBindingPattern sourceSpan =>
      at sourceSpan "This pattern does not match every value; a binding needs an irrefutable pattern."
    MultiplicityMismatch required actual sourceSpan =>
      at sourceSpan $ "Expected a '" ++ show required ++ "' qbit, but found a '" ++ show actual ++ "' qbit; use weaken to make a linear qbit affine."
    BreakValueInUnitLoop sourceSpan =>
      at sourceSpan "A 'while' or 'for' loop cannot break with a value."
    AssignmentThroughSharedReference sourceSpan =>
      at sourceSpan "Cannot assign through a shared reference."
    InvalidAttributeEffect attribute effect sourceSpan =>
      at sourceSpan $ "The attribute '" ++ attribute ++ "' is not allowed on a function with effect '" ++ show effect ++ "'."
    JumpOutOfQuantumBlock jump sourceSpan =>
      at sourceSpan $ "'" ++ jump ++ "' cannot leave a ctrl or adjoint block."
    LinearQbitNotConsumed sourceSpan =>
      at sourceSpan "A linear qbit is never consumed; measure, discard or return it."
    UseAfterMove name sourceSpan =>
      at sourceSpan $ "Use of '" ++ name ++ "' after it was moved."
    UntrackedElementMove sourceSpan =>
      at sourceSpan "Cannot move an array element out through a dynamic index."
    MoveOutOfBorrow sourceSpan =>
      at sourceSpan "Cannot move a qbit out through a reference."
    OverlappingBorrow sourceSpan =>
      at sourceSpan "This access conflicts with a live exclusive borrow."
    MutableBorrowOfImmutable name sourceSpan =>
      at sourceSpan $ "Cannot borrow '" ++ name ++ "' mutably; declare it with 'mut'."
    ImmutableAssignment name sourceSpan =>
      at sourceSpan $ "Cannot assign twice to immutable '" ++ name ++ "'; declare it with 'mut'."
    UninitializedPlace name sourceSpan =>
      at sourceSpan $ "'" ++ name ++ "' is used before it is initialized."
    EscapingReference sourceSpan =>
      at sourceSpan "This reference outlives the value it refers to."
    UnprovableCleanup sourceSpan =>
      at sourceSpan "Cannot prove that these qubits can be uncomputed and released."
    UnprovableTransformation transformation sourceSpan =>
      at sourceSpan $ "Cannot construct the '" ++ transformation ++ "' transformation of this code."
  where
    at : SourceSpan -> String -> String
    at sourceSpan message = "Type error at \{sourceSpan}: \{message}"

public export
implementation Show TypeError where
  show = showTypeError

