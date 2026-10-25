module Compiler.Validation.PostParseValidation

import Data.List
import Data.List1
import Frontend.ASTData
import Frontend.ASTPhases
import Frontend.Source
import Frontend.Token
import Frontend.Syntax.AST
import Frontend.Syntax.Attribute
import Frontend.Syntax.Common
import Frontend.Syntax.Literal
import Frontend.Syntax.Name
import Frontend.Syntax.Operator
import Frontend.Syntax.Type

%default total

--------------------------------------------------------------------------------
-- Post-parse syntactic validation
--------------------------------------------------------------------------------
-- The pass that owns every check which is (a) NOT enforced by the AST's
-- shape, (b) NOT a parser rejection, and (c) decidable on the SURFACE TREE
-- ALONE -- no name resolution, no types. It runs immediately after parsing
-- and reports against the spans the AST preserved for exactly this purpose.
--
-- CHECKS OWNED HERE:
--   * unknown attribute names: only `qasm_gate` and `qasm_def` are
--       recognized
--   * duplicate attributes on one item: a repeated name is rejected at its
--       second occurrence
--   * conflicting attributes on one item: `qasm_gate` and `qasm_def` are
--       mutually exclusive and are rejected when applied together
--   * `&mut` on a SYNTACTICALLY-qubit type (`&mut qubit`, `&mut [qubit]`,
--       `&mut [qubit; 2]`, through parens/qualifiers), wherever a type occurs;
--   * `break` outside a loop, while still walking and validating its optional
--       value expression
--   * `continue` outside a loop
--   * `return` outside a function body (for example in a const initializer),
--       while still walking and validating its optional value expression
--   * an ownership qualifier written both on a `let` and inside its type
--       annotation (`let linear q: affine qubit = ...`); reported at every
--       qualifier at an owned position of the annotation (see "Owned
--       positions" in Frontend.Syntax.Type), so qualifiers inside function
--       types are not repeats
--   * an ownership qualifier behind a reference, nested in its referent
--       (`&[linear qubit]`, `&(i32, affine qubit)`): a reference borrows its
--       referent without owning it; the parser already rejects one directly
--       after `&` (`&affine qubit`)
--   * an array length written as a (possibly parenthesized) integer literal
--       with a signed type suffix (`[qubit; 3i8]`, `[0; (3i8)]`) or a value
--       that does not fit its unsigned suffix type (`[qubit; 256u8]`): an
--       array length is unsigned, so only an unsigned suffix or none is
--       accepted
--
-- Duplicate bindings are checked by name resolution: an immutable bare
-- pattern name may denote a constant rather than introduce a binding.
-- This applies to function parameters as well as let and for patterns.
--
-- Shape of the pass: a plain structural walk accumulating a List of errors
-- (empty list = valid). No early exit -- diagnostics improve when the user
-- sees every independent problem at once.
--
-- TOTALITY DISCIPLINE:
-- Idris 2's size-change checker credits CONSTRUCTOR PATTERNS ONLY. A record
-- dot-projection feeding a recursive argument (`validateBlock ctx
-- fd.functionBody`) is size-unknown, and one unknown edge poisons the whole
-- SCC -- and this walk is ONE SCC, because expressions and types are mutual
-- (casts contain types; array sizes contain expressions). So: destructure
-- every record in the pattern head or in a constructor pattern; never
-- project in a recursive position. Projections remain fine on non-recursive
-- data (ValidationContext, SourceSpan).
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Validation errors
--------------------------------------------------------------------------------

public export
data ValidationError : Type where

  UnknownAttribute :
       (errorSpan : SourceSpan)
    -> (attributeNameText : String)
    -> ValidationError

  -- Same attribute name written twice on one item, e.g.
  -- `#[qasm_gate] #[qasm_gate] fn f() {}`. `errorSpan` points at the
  -- repeated (second) occurrence.
  DuplicateAttribute :
       (errorSpan : SourceSpan)
    -> (attributeNameText : String)
    -> ValidationError

  -- Two distinct KNOWN attributes on one item, e.g.
  -- `#[qasm_gate] #[qasm_def] fn f() {}`. Today's only known attributes,
  -- qasm_gate and qasm_def, name mutually exclusive compilation targets, so
  -- any two distinct known attributes together are a conflict; `errorSpan`
  -- points at the second one.
  ConflictingAttributes :
       (errorSpan : SourceSpan)
    -> (attributeNameText : String)
    -> ValidationError

  MutableBorrowOfQubit :
       (errorSpan : SourceSpan)
    -> ValidationError

  BreakOutsideLoop :
       (errorSpan : SourceSpan)
    -> ValidationError

  ContinueOutsideLoop :
       (errorSpan : SourceSpan)
    -> ValidationError

  ReturnOutsideFunction :
       (errorSpan : SourceSpan)
    -> ValidationError

  ControlBasisLengthMismatch :
       (errorSpan : SourceSpan)
    -> (controlCount : Nat)
    -> (basisLength : Nat)
    -> ValidationError

  -- An ownership qualifier written both on a `let` and inside its type
  -- annotation, e.g. `let linear q: affine qubit = qalloc();`. `errorSpan`
  -- points at the qualifier inside the annotation.
  OwnershipQualifierInLetAndType :
       (errorSpan : SourceSpan)
    -> (letQualifier : OwnershipQualifier)
    -> (typeQualifier : OwnershipQualifier)
    -> ValidationError

  -- An ownership qualifier at an owned position of a reference's referent,
  -- e.g. `&[linear qubit]`. `errorSpan` points at the qualifier.
  OwnershipQualifierBehindReference :
       (errorSpan : SourceSpan)
    -> (qualifier : OwnershipQualifier)
    -> ValidationError

  -- An array length written as an integer literal with a signed type
  -- suffix, e.g. `[qubit; 3i8]`. `errorSpan` points at the literal.
  SignedArrayLength :
       (errorSpan : SourceSpan)
    -> (suffixType : TypPrimName)
    -> ValidationError

  -- An array length written as an integer literal whose value does not fit
  -- its suffix type, e.g. `[qubit; 256u8]`. `errorSpan` points at the literal.
  ArrayLengthOutOfRange :
       (errorSpan : SourceSpan)
    -> (literalText : String)
    -> (suffixType : TypPrimName)
    -> (suffixMaximum : Nat)
    -> ValidationError

-- The span a renderer should point at.
public export
validationErrorSpan : ValidationError -> SourceSpan
validationErrorSpan err =
  case err of
    UnknownAttribute s _        => s
    DuplicateAttribute s _      => s
    ConflictingAttributes s _   => s
    MutableBorrowOfQubit s      => s
    BreakOutsideLoop s          => s
    ContinueOutsideLoop s       => s
    ReturnOutsideFunction s     => s
    ControlBasisLengthMismatch s _ _ => s
    OwnershipQualifierInLetAndType s _ _ => s
    OwnershipQualifierBehindReference s _ => s
    SignedArrayLength s _ => s
    ArrayLengthOutOfRange s _ _ _ => s

withValidationErrorFile : String -> ValidationError -> ValidationError
withValidationErrorFile fileName err =
  let withFile : SourceSpan =
        { file := fileName } (validationErrorSpan err)
  in case err of
       UnknownAttribute _ nameText        => UnknownAttribute withFile nameText
       DuplicateAttribute _ nameText      => DuplicateAttribute withFile nameText
       ConflictingAttributes _ nameText   => ConflictingAttributes withFile nameText
       MutableBorrowOfQubit _             => MutableBorrowOfQubit withFile
       BreakOutsideLoop _                 => BreakOutsideLoop withFile
       ContinueOutsideLoop _              => ContinueOutsideLoop withFile
       ReturnOutsideFunction _            => ReturnOutsideFunction withFile
       ControlBasisLengthMismatch _ controlCount basisLength =>
         ControlBasisLengthMismatch withFile controlCount basisLength
       OwnershipQualifierInLetAndType _ letQualifier typeQualifier =>
         OwnershipQualifierInLetAndType withFile letQualifier typeQualifier
       OwnershipQualifierBehindReference _ qualifier =>
         OwnershipQualifierBehindReference withFile qualifier
       SignedArrayLength _ suffixType =>
         SignedArrayLength withFile suffixType
       ArrayLengthOutOfRange _ literalText suffixType suffixMaximum =>
         ArrayLengthOutOfRange withFile literalText suffixType suffixMaximum

-- "file:line:col" prefix, matching the lexer-error rendering style.
renderSpanPrefix : SourceSpan -> String
renderSpanPrefix s =
  s.file ++ ":" ++ show s.start.line ++ ":" ++ show s.start.column

public export
Interpolation ValidationError where
  interpolate err =
    renderSpanPrefix (validationErrorSpan err) ++ ": " ++
      case err of
        UnknownAttribute _ nm =>
          "unknown attribute `" ++ nm ++
          "` (supported: qasm_gate, qasm_def)"
        DuplicateAttribute _ nm =>
          "attribute `" ++ nm ++
          "` is already applied to this item"
        ConflictingAttributes _ nm =>
          "attribute `" ++ nm ++
          "` conflicts with another attribute already applied to this item " ++
          "(qasm_gate and qasm_def are mutually exclusive)"
        MutableBorrowOfQubit _ =>
          "`mut` should never be written on a qubit reference; qubit references are mutable by default"
        BreakOutsideLoop _ =>
          "`break` found outside of a loop"
        ContinueOutsideLoop _ =>
          "`continue` found outside of a loop"
        ReturnOutsideFunction _ =>
          "`return` found outside of a function body"
        ControlBasisLengthMismatch _ controlCount basisLength =>
          "control basis contains " ++ show basisLength ++
          " states, but the control expression has " ++ show controlCount ++
          " control qubits"
        OwnershipQualifierInLetAndType _ letQualifier typeQualifier =>
          "`" ++ show typeQualifier ++ "` cannot be written in the type " ++
          "annotation because the `let` already has the `" ++ show letQualifier ++
          "` qualifier; write the ownership qualifier in one place only"
        OwnershipQualifierBehindReference _ qualifier =>
          "`" ++ show qualifier ++ "` cannot be written behind a reference; " ++
          "a reference borrows its referent without owning it"
        SignedArrayLength _ suffixType =>
          "an array length cannot have the signed type suffix `" ++
          show suffixType ++ "`; write an unsigned suffix such as `u32`, or none"
        ArrayLengthOutOfRange _ literalText suffixType suffixMaximum =>
          "the array length `" ++ literalText ++ "` does not fit in `" ++
          show suffixType ++ "`, whose largest value is " ++ show suffixMaximum

--------------------------------------------------------------------------------
-- Validation context
--------------------------------------------------------------------------------
-- The little positional state the walk threads. Note the Rust rule encoded
-- at the while/for sites below: the CONDITION of a while and the ITERATOR
-- expression of a for are validated with insideLoop = False -- a break
-- there does not target the loop it syntactically sits in.
--------------------------------------------------------------------------------

record ValidationContext where
  constructor MkValidationContext
  insideLoop         : Bool
  insideFunctionBody : Bool

-- Top level / signatures / const initializers.
topLevelContext : ValidationContext
topLevelContext = MkValidationContext False False

-- Entering a function body.
functionBodyContext : ValidationContext
functionBodyContext = MkValidationContext False True

--------------------------------------------------------------------------------
-- Leaf checks (no traversal needed)
--------------------------------------------------------------------------------

-- Do two known attribute kinds conflict when both are written on one item?
-- The only known kinds today, qasm_gate and qasm_def, name mutually
-- exclusive OpenQASM compilation targets and the spec never shows more than
-- one of them on the same function -- so any two DISTINCT known kinds
-- conflict.
knownAttributeKindsConflict : KnownAttributeKind -> KnownAttributeKind -> Bool
knownAttributeKindsConflict KnownQasmGate KnownQasmGate = False
knownAttributeKindsConflict KnownQasmDef  KnownQasmDef  = False
knownAttributeKindsConflict _             _             = True

-- Known attributes: unknown names are errors for now. Argument shape is not
-- checked here: `parseAttribute` already accepts nothing but `#[name]` or
-- `#[name("string")]`, so every attribute reaching this pass is already
-- well-shaped.
--
-- Walks the list left-to-right threading the (name, known-kind) pairs
-- already seen on THIS item, so a name repeated verbatim is
-- DuplicateAttribute and two distinct known kinds together (currently just
-- qasm_gate + qasm_def) is ConflictingAttributes.
validateAttributeListFrom :
     List (String, Maybe KnownAttributeKind)
  -> List SurfaceAttribute
  -> List ValidationError
validateAttributeListFrom _ [] = []
validateAttributeListFrom seen (MkAstNode attrInfo _ (MkAttributeNode nameNode _) :: rest) =
  let MkAstNode _ _ (MkNameNode nameText) = nameNode
      thisKind = recognizeKnownAttribute nameText
      unknownError =
        case thisKind of
          Nothing => [UnknownAttribute attrInfo.span nameText]
          Just _  => []
      duplicateError =
        if any (\s => fst s == nameText) seen
          then [DuplicateAttribute attrInfo.span nameText]
          else []
      conflictError =
        case thisKind of
          Nothing => []
          Just k  =>
            if any (\s => maybe False (knownAttributeKindsConflict k) (snd s)) seen
              then [ConflictingAttributes attrInfo.span nameText]
              else []
  in unknownError ++ duplicateError ++ conflictError
       ++ validateAttributeListFrom ((nameText, thisKind) :: seen) rest

validateAttributeList : List SurfaceAttribute -> List ValidationError
validateAttributeList = validateAttributeListFrom []

-- Is this type SYNTACTICALLY a qubit-carrying type? Only the cases visible
-- without resolution: qubit itself, arrays/slices of it, through parens and
-- qualifiers. Path types that CONTAIN qubits are typing's problem.
isSyntacticallyQubitTy : TyNode SurfaceAstPhase SurfaceExpr -> Bool
isSyntacticallyQubitTy ty =
  case ty of
    TyPrimitive TypPrimQubit                   => True
    TyParenthesized (MkAstNode _ _ inner)      => isSyntacticallyQubitTy inner
    TyQualified _ (MkAstNode _ _ inner)        => isSyntacticallyQubitTy inner
    TySlice (MkAstNode _ _ element)            => isSyntacticallyQubitTy element
    TyArray (MkAstNode _ _ element) _          => isSyntacticallyQubitTy element
    _                                          => False

-- Ownership qualifiers written at the owned positions of a type.
ownedPositionQualifiers : SurfaceTy -> List (SurfaceAstNode OwnershipQualifier)
ownedPositionQualifiers = mapMaybe positionQualifier . ownedPositions

-- A `let` carrying `linear` or `affine` must not repeat an ownership qualifier
-- inside its type annotation. `scratch` on the `let` is unaffected.
letOwnershipConflicts :
     List (AstNode SurfaceAstPhase QuantumStorageQualifier)
  -> Maybe SurfaceTy
  -> List ValidationError
letOwnershipConflicts _ Nothing = []
letOwnershipConflicts letQualifiers (Just annotation) =
  case mapMaybe (storageOwnership . (.value)) letQualifiers of
    [] => []
    letQualifier :: _ =>
      map (\(MkAstNode qualifierInfo _ typeQualifier) =>
             OwnershipQualifierInLetAndType qualifierInfo.span letQualifier typeQualifier)
          (ownedPositionQualifiers annotation)

-- A reference's referent holds no ownership qualifier at an owned position.
-- Qualifiers behind a nested reference are reported when the walk reaches
-- that reference, since owned positions do not enter references.
qualifiersBehindReference : SurfaceTy -> List ValidationError
qualifiersBehindReference referent =
  map (\(MkAstNode qualifierInfo _ qualifier) =>
         OwnershipQualifierBehindReference qualifierInfo.span qualifier)
      (ownedPositionQualifiers referent)

-- An array length written as an integer literal may carry only an unsigned
-- type suffix, and its value must fit that type. Parentheses are looked
-- through because desugaring removes them, leaving the bare literal for
-- typing. Lengths computed by other expressions are left to typing.
arrayLengthErrors : SurfaceExpr -> List ValidationError
arrayLengthErrors (MkAstNode _ _ (ExprParenthesized innerLength)) =
  arrayLengthErrors innerLength
arrayLengthErrors
    (MkAstNode lengthInfo _ (ExprLiteral (MkAstNode _ _ (LiteralIntegerRaw raw)))) =
  case arrayLengthProblem raw of
    Just (SignedLengthSuffix suffixType) =>
      [SignedArrayLength lengthInfo.span suffixType]
    Just (LengthExceedsSuffixType suffixType suffixMaximum) =>
      [ArrayLengthOutOfRange lengthInfo.span raw suffixType suffixMaximum]
    Nothing => []
arrayLengthErrors _ = []

--------------------------------------------------------------------------------
-- The traversal
--------------------------------------------------------------------------------
-- Every function here destructures records with constructor patterns, per
-- the totality discipline in the header. Unused fields are wildcards; the
-- field ORDER in each pattern must track the record declarations in AST.idr.
--------------------------------------------------------------------------------

mutual

  -- Entry point: validate one parsed source file.
  public export
  validateSourceFile : SurfaceSourceFile -> List ValidationError
  validateSourceFile (MkAstNode fileInfo _ (MkSourceFileNode _ items)) =
    map (withValidationErrorFile fileInfo.span.file) (validateItemList items)

  ------------------------------------------------------------------
  -- Items and declarations
  ------------------------------------------------------------------

  validateItemList : List SurfaceItem -> List ValidationError
  validateItemList [] = []
  validateItemList (i :: rest) = validateItem i ++ validateItemList rest

  validateItem : SurfaceItem -> List ValidationError
  validateItem (MkAstNode _ _ item) =
    case item of
      ItemFunction fd => validateFunctionDecl fd
      ItemStruct sd   => validateStructDecl sd
      ItemEnum ed     => validateEnumDecl ed
      ItemQEnum qd    => validateQEnumDecl qd
      ItemImpl impl   => validateImplDecl impl
      ItemConst cd    => validateConstDecl cd
      -- `use` has no attributes, types, or expressions to walk.
      ItemUse _       => []
      ItemModule md   => validateModuleDecl md

  -- Fields (in declaration order): docs, attributes, visibility, constness,
  -- effect, name, parameters, returnType, supports, contracts, body.
  -- `supports` and `contracts` are not walked here: the parser rejects
  -- `supports` and `requires`/`ensures` outright, so those fields are
  -- always empty by construction.
  validateFunctionDecl : FunctionDeclarationNode SurfaceAstPhase -> List ValidationError
  validateFunctionDecl
    (MkFunctionDeclarationNode _ attrs _ _ _ _ params retTy _ _ body) =
       validateAttributeList attrs
    ++ validateParameterList params
    ++ validateMaybeTy topLevelContext retTy
    ++ validateBlock functionBodyContext body

  -- Parameter names require resolution, but every type still needs the
  -- syntactic and contextual checks performed by this pass.
  validateParameterList : List SurfaceFunctionParameter -> List ValidationError
  validateParameterList [] = []
  validateParameterList (MkAstNode _ _ p :: rest) =
    case p of
      NormalParameter _ _ _ ty =>
        validateTy topLevelContext ty ++ validateParameterList rest
      ReceiverParameter _ _ =>
        validateParameterList rest

  validateStructDecl : StructDeclarationNode SurfaceAstPhase -> List ValidationError
  validateStructDecl (MkStructDeclarationNode _ attrs _ _ fields) =
       validateAttributeList attrs
    ++ validateStructFieldList fields

  validateStructFieldList :
       List (AstNode SurfaceAstPhase (StructFieldNode SurfaceAstPhase))
    -> List ValidationError
  validateStructFieldList [] = []
  validateStructFieldList
    (MkAstNode _ _ (MkStructFieldNode _ _ fieldTy) :: rest) =
    validateTy topLevelContext fieldTy ++ validateStructFieldList rest

  validateEnumDecl : EnumDeclarationNode SurfaceAstPhase -> List ValidationError
  validateEnumDecl (MkEnumDeclarationNode _ attrs _ _ variants) =
       validateAttributeList attrs
    ++ validateEnumVariantList variants

  validateEnumVariantList :
       List (AstNode SurfaceAstPhase (EnumVariantNode SurfaceAstPhase))
    -> List ValidationError
  validateEnumVariantList [] = []
  validateEnumVariantList
    (MkAstNode _ _ (MkEnumVariantNode _ _ body) :: rest) =
    (case body of
       VariantUnit            => []
       VariantTuple tys       => validateTyList1 topLevelContext tys
       VariantStruct fields   => validateStructFieldList fields)
      ++ validateEnumVariantList rest

  validateQEnumDecl : QEnumDeclarationNode SurfaceAstPhase -> List ValidationError
  validateQEnumDecl (MkQEnumDeclarationNode _ attrs _ _ variants) =
       validateAttributeList attrs
    ++ validateQEnumVariantList variants

  validateQEnumVariantList :
       List (AstNode SurfaceAstPhase (QEnumVariantNode SurfaceAstPhase))
    -> List ValidationError
  validateQEnumVariantList [] = []
  validateQEnumVariantList
    (MkAstNode _ _ (MkQEnumVariantNode _ _ payloadTys) :: rest) =
    validateTyList1 topLevelContext payloadTys
      ++ validateQEnumVariantList rest

  validateImplDecl : ImplDeclarationNode SurfaceAstPhase -> List ValidationError
  validateImplDecl (MkImplDeclarationNode _ _ fns) =
    validateImplFunctionList fns

  validateImplFunctionList :
       List SurfaceFunctionDeclaration
    -> List ValidationError
  validateImplFunctionList [] = []
  validateImplFunctionList (MkAstNode _ _ fd :: rest) =
    validateFunctionDecl fd ++ validateImplFunctionList rest

  -- Const initializers are NOT function bodies: `return` inside one is an
  -- error, which topLevelContext encodes.
  validateConstDecl : ConstDeclarationNode SurfaceAstPhase -> List ValidationError
  validateConstDecl (MkConstDeclarationNode _ _ _ constTy constVal) =
       validateTy topLevelContext constTy
    ++ validateExpr topLevelContext constVal

  validateModuleDecl : ModuleDeclarationNode SurfaceAstPhase -> List ValidationError
  validateModuleDecl (MkModuleDeclarationNode _ _ _ body) =
    case body of
      ModuleInline _ items => validateItemList items
      ModuleExternal       => []

  ------------------------------------------------------------------
  -- Blocks and statements
  ------------------------------------------------------------------

  validateBlock : ValidationContext -> SurfaceBlock -> List ValidationError
  validateBlock ctx (MkAstNode _ _ (MkBlockNode _ stmts finalE)) =
       validateStatementList ctx stmts
    ++ validateMaybeExpr ctx finalE

  validateStatementList : ValidationContext -> List SurfaceStatement -> List ValidationError
  validateStatementList ctx [] = []
  validateStatementList ctx (s :: rest) =
    validateStatement ctx s ++ validateStatementList ctx rest

  validateStatement : ValidationContext -> SurfaceStatement -> List ValidationError
  validateStatement ctx (MkAstNode _ _ stmt) =
    case stmt of
      StatementLet (MkLetBindingNode letQualifiers _ tyAnn maybeInit) =>
           letOwnershipConflicts letQualifiers tyAnn
        ++ validateMaybeTy ctx tyAnn
        ++ (case maybeInit of
              Nothing => []
              Just (MkLetInitializerNode _ initValue) =>
                validateExpr ctx initValue)
      StatementAssignment (MkAssignmentNode target _ assignValue) =>
           validateAssignmentTarget ctx target
        ++ validateExpr ctx assignValue
      StatementSemiExpression e => validateExpr ctx e
      StatementExpression e     => validateExpr ctx e

  validateAssignmentTarget : ValidationContext -> SurfaceAssignmentTarget -> List ValidationError
  validateAssignmentTarget ctx (MkAstNode _ _ target) =
    case target of
      AssignTargetName _             => []
      AssignTargetIndex obj idx      =>
        validateExpr ctx obj ++ validateExpr ctx idx
      AssignTargetField obj _        => validateExpr ctx obj
      AssignTargetTupleIndex obj _   => validateExpr ctx obj

  ------------------------------------------------------------------
  -- Expressions
  ------------------------------------------------------------------

  validateExprList :
       ValidationContext -> List SurfaceExpr -> List ValidationError
  validateExprList ctx [] = []
  validateExprList ctx (e :: rest) =
    validateExpr ctx e ++ validateExprList ctx rest

  validateExprList1 :
       ValidationContext -> List1 SurfaceExpr -> List ValidationError
  validateExprList1 ctx (e ::: rest) =
    validateExpr ctx e ++ validateExprList ctx rest

  validateMaybeExpr :
       ValidationContext -> Maybe SurfaceExpr -> List ValidationError
  validateMaybeExpr ctx Nothing  = []
  validateMaybeExpr ctx (Just e) = validateExpr ctx e

  validateExpr : ValidationContext -> SurfaceExpr -> List ValidationError
  validateExpr ctx (MkAstNode info _ expr) =
    case expr of
      ExprLiteral _  => []
      ExprName _     => []
      ExprBuiltin _  => []

      ExprParenthesized e   => validateExpr ctx e
      ExprTuple es          => validateExprList1 ctx es
      ExprArray es          => validateExprList ctx es
      ExprRepeatedArray e c =>
        validateExpr ctx e ++ arrayLengthErrors c ++ validateExpr ctx c

      ExprCall callee args =>
        validateExpr ctx callee ++ validateExprList ctx args
      ExprMethodCall recv _ args =>
        validateExpr ctx recv ++ validateExprList ctx args
      ExprField obj _        => validateExpr ctx obj
      ExprTupleIndex obj _   => validateExpr ctx obj
      ExprIndex obj idx      => validateExpr ctx obj ++ validateExpr ctx idx

      ExprUnary _ operand    => validateExpr ctx operand
      ExprBinary _ lhs rhs   => validateExpr ctx lhs ++ validateExpr ctx rhs
      ExprRange s _ e        => validateMaybeExpr ctx s ++ validateMaybeExpr ctx e
      ExprCast e ty          => validateExpr ctx e ++ validateTy ctx ty

      ExprBlock b            => validateBlock ctx b

      ExprIf ifNode          => validateClassicalIf ctx ifNode

      -- Loop bodies set insideLoop; while conditions and for iterator
      -- expressions do NOT count as inside the loop they head.
      ExprLoop body =>
        validateBlock (MkValidationContext True ctx.insideFunctionBody) body
      ExprWhile cond body =>
           validateExpr (MkValidationContext False ctx.insideFunctionBody) cond
        ++ validateBlock (MkValidationContext True ctx.insideFunctionBody) body
      ExprFor _ iterExpr body =>
           validateExpr (MkValidationContext False ctx.insideFunctionBody) iterExpr
        ++ validateBlock (MkValidationContext True ctx.insideFunctionBody) body

      ExprBreak breakValue =>
        (if ctx.insideLoop then [] else [BreakOutsideLoop info.span])
          ++ validateMaybeExpr ctx breakValue
      ExprContinue =>
        if ctx.insideLoop then [] else [ContinueOutsideLoop info.span]
      ExprReturn returnValue =>
        (if ctx.insideFunctionBody then [] else [ReturnOutsideFunction info.span])
          ++ validateMaybeExpr ctx returnValue

      ExprCtrl c    => validateControlExpr ctx c
      ExprAdjoint a => validateAdjointExpr ctx a

      ExprStructLiteral _ fields => validateFieldInitList ctx fields

      ExprQIf (MkQuantumIfNode qifCond thenBranch elseBranch) =>
           validateExpr ctx qifCond
        ++ validateQuantumBranch ctx thenBranch
        ++ (case elseBranch of
              Nothing => []
              Just b  => validateQuantumBranch ctx b)
      ExprSIf (MkStateIfNode sifCond thenE elseE) =>
           validateExpr ctx sifCond
        ++ validateExpr ctx thenE
        ++ validateExpr ctx elseE

      ExprMatch (MkClassicalMatchNode scrut arms) =>
           validateExpr ctx scrut
        ++ validateClassicalArmList ctx arms
      ExprQMatch (MkQuantumMatchNode scrut arms) =>
           validateExpr ctx scrut
        ++ validateQuantumArmBodies ctx arms
      ExprSMatch (MkStateMatchNode scrut arms) =>
           validateExpr ctx scrut
        ++ validateQuantumArmBodies ctx arms

      -- ExprPath/ExprSelf carry no sub-expressions to walk. All eight forms
      -- above are also rejected as unsupported by the current parser, so a
      -- parsed source file cannot contain them yet -- but walking them now
      -- costs nothing and means nothing needs revisiting once the parser
      -- catches up. Their own semantic checks (qmatch/smatch pattern
      -- homogeneity, contract ordering, duplicate supports) stay out until
      -- that syntax exists to check.
      ExprPath _ => []
      ExprSelf _ => []

  validateFieldInitList :
       ValidationContext
    -> List (AstNode SurfaceAstPhase (FieldInitializerNode SurfaceAstPhase))
    -> List ValidationError
  validateFieldInitList ctx [] = []
  validateFieldInitList ctx (MkAstNode _ _ f :: rest) =
    (case f of
       FieldInitShorthand _   => []
       FieldInitExplicit _ e  => validateExpr ctx e)
      ++ validateFieldInitList ctx rest

  validateClassicalIf :
       ValidationContext -> ClassicalIfNode SurfaceAstPhase -> List ValidationError
  validateClassicalIf ctx (MkClassicalIfNode ifCond thenBlock elseBranch) =
       validateExpr ctx ifCond
    ++ validateBlock ctx thenBlock
    ++ (case elseBranch of
          Nothing                => []
          Just (ElseBlock b)     => validateBlock ctx b
          Just (ElseChainedIf (MkAstNode _ _ chained)) =>
            validateClassicalIf ctx chained)

  validateQuantumBranch :
       ValidationContext -> QuantumBranchNode SurfaceAstPhase -> List ValidationError
  validateQuantumBranch ctx branch =
    case branch of
      QuantumBranchBlock b      => validateBlock ctx b
      QuantumBranchExpression e => validateExpr ctx e

  validateClassicalArmList :
       ValidationContext
    -> List SurfaceClassicalMatchArm
    -> List ValidationError
  validateClassicalArmList ctx [] = []
  validateClassicalArmList ctx
    (MkAstNode _ _ (MkClassicalMatchArmNode _ guard armBody) :: rest) =
       validateMaybeExpr ctx guard
    ++ validateExpr ctx armBody
    ++ validateClassicalArmList ctx rest

  validateQuantumArmBodies :
       ValidationContext
    -> List SurfaceQuantumMatchArm
    -> List ValidationError
  validateQuantumArmBodies ctx [] = []
  validateQuantumArmBodies ctx
    (MkAstNode _ _ (MkQuantumMatchArmNode _ armBody) :: rest) =
    validateExpr ctx armBody ++ validateQuantumArmBodies ctx rest

  validateControlBasis :
      List1 SurfaceExpr -> Maybe (SurfaceAstNode String) -> List ValidationError
  validateControlBasis _ Nothing = []
  validateControlBasis controls
      (Just (MkAstNode basisInfo _ rawBasis)) =
    let controlCount = length controls
        basisLength = length (unpack rawBasis) `minus` 4
    in if controlCount == basisLength
        then []
        else [ControlBasisLengthMismatch basisInfo.span controlCount basisLength]

  validateControlExpr :
       ValidationContext -> ControlExpressionNode SurfaceAstPhase -> List ValidationError
  validateControlExpr ctx c =
    case c of
      ControlledCallable controls onBasis callable =>
          validateControlBasis controls onBasis
        ++ validateExprList1 ctx controls
        ++ validateExpr ctx callable

      ControlledBlock controls onBasis body =>
          validateControlBasis controls onBasis
        ++ validateExprList1 ctx controls
        ++ validateBlock ctx body

  validateAdjointExpr :
       ValidationContext -> AdjointExpressionNode SurfaceAstPhase -> List ValidationError
  validateAdjointExpr ctx a =
    case a of
      AdjointOfCallable callable => validateExpr ctx callable
      AdjointBlock body          => validateBlock ctx body

  ------------------------------------------------------------------
  -- Types: the &mut-qubit check, the qualifier-behind-reference check, the
  -- array-length literal check, and recursion into array-size expressions
  -- (which are full surface expressions).
  ------------------------------------------------------------------

  validateTyList :
       ValidationContext -> List SurfaceTy -> List ValidationError
  validateTyList ctx [] = []
  validateTyList ctx (t :: rest) =
    validateTy ctx t ++ validateTyList ctx rest

  validateTyList1 :
       ValidationContext -> List1 SurfaceTy -> List ValidationError
  validateTyList1 ctx (t ::: rest) =
    validateTy ctx t ++ validateTyList ctx rest

  validateMaybeTy :
       ValidationContext -> Maybe SurfaceTy -> List ValidationError
  validateMaybeTy ctx Nothing  = []
  validateMaybeTy ctx (Just t) = validateTy ctx t

  validateTy : ValidationContext -> SurfaceTy -> List ValidationError
  validateTy ctx (MkAstNode _ _ ty) =
    case ty of
      TyPrimitive _        => []
      TyPath _             => []
      TyUnit               => []
      TyParenthesized t    => validateTy ctx t
      TyTuple ts           => validateTyList1 ctx ts
      TyArray element size =>
        validateTy ctx element ++ arrayLengthErrors size ++ validateExpr ctx size
      TySlice element      => validateTy ctx element
      TyReference (MkAstNode borrowInfo _ borrow)
                  innerNode@(MkAstNode _ _ innerTy) =>
        (case borrow of
           MutableBorrow =>
             if isSyntacticallyQubitTy innerTy
               then [MutableBorrowOfQubit borrowInfo.span]
               else []
           SharedBorrow  => [])
          ++ qualifiersBehindReference innerNode
          ++ validateTy ctx innerNode
      TyQualified _ inner => validateTy ctx inner
      TyFunction _ params returnTy =>
        validateFunctionTypeParams ctx params
          ++ validateMaybeTy ctx returnTy

  validateFunctionTypeParams :
       ValidationContext
    -> List (AstNode SurfaceAstPhase (FunctionTypeParameterNode SurfaceAstPhase SurfaceExpr))
    -> List ValidationError
  validateFunctionTypeParams ctx [] = []
  validateFunctionTypeParams ctx
    (MkAstNode _ _ (MkFunctionTypeParameterNode _ paramTy) :: rest) =
    validateTy ctx paramTy ++ validateFunctionTypeParams ctx rest
