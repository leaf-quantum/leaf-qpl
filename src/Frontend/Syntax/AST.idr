module Frontend.Syntax.AST

import Data.List1
import Frontend.Token
import Frontend.ASTPhases
import Frontend.Syntax.Attribute
import Frontend.Syntax.Common
import Frontend.Syntax.Contract
import Frontend.Syntax.Doc
import Frontend.Syntax.Literal
import Frontend.Syntax.Name
import Frontend.Syntax.Operator
import Frontend.Syntax.Pattern
import Frontend.Syntax.Type

%default total

--------------------------------------------------------------------------------
-- The central mutually recursive AST, indexed by AstPhase
--------------------------------------------------------------------------------
-- Everything mutually recursive lives in this one module: programs, items,
-- declarations, blocks, statements, and expressions. The leaf modules
-- (Name, Doc, Literal, Operator, Common, Attribute, Pattern) are acyclic;
-- Type and Contract are parameterized over the expression type, and THIS
-- module ties both knots:
--
--   SurfaceTy             = Ty SurfaceAstPhase SurfaceExpr
--   SurfaceContractClause = ContractClause SurfaceAstPhase SurfaceExpr
--------------------------------------------------------------------------------

mutual

  ------------------------------------------------------------------------------
  -- aliases (defined first; mutual-block visibility makes the
  -- forward references to the node families below legal)
  ------------------------------------------------------------------------------

  public export
  Expr : AstPhase -> Type
  Expr phase = AstNode phase (ExpressionNode phase)

  public export
  SurfaceExpr : Type
  SurfaceExpr = Expr SurfaceAstPhase

  public export
  CanonicalExpr : Type
  CanonicalExpr = Expr CanonicalAstPhase

  public export
  ResolvedExpr : Type
  ResolvedExpr = Expr ResolvedAstPhase

  public export
  TypedExpr : Type
  TypedExpr = Expr TypedAstPhase

  public export
  Block : AstPhase -> Type
  Block phase = AstNode phase (BlockNode phase)

  public export
  SurfaceBlock : Type
  SurfaceBlock = Block SurfaceAstPhase

  public export
  CanonicalBlock : Type
  CanonicalBlock = Block CanonicalAstPhase

  public export
  ResolvedBlock : Type
  ResolvedBlock = Block ResolvedAstPhase

  public export
  TypedBlock : Type
  TypedBlock = Block TypedAstPhase

  public export
  Statement : AstPhase -> Type
  Statement phase = AstNode phase (StatementNode phase)

  public export
  SurfaceStatement : Type
  SurfaceStatement = Statement SurfaceAstPhase

  public export
  CanonicalStatement : Type
  CanonicalStatement = Statement CanonicalAstPhase

  public export
  ResolvedStatement : Type
  ResolvedStatement = Statement ResolvedAstPhase

  public export
  TypedStatement : Type
  TypedStatement = Statement TypedAstPhase

  public export
  Item : AstPhase -> Type
  Item phase = AstNode phase (ItemNode phase)

  public export
  SurfaceItem : Type
  SurfaceItem = Item SurfaceAstPhase

  public export
  CanonicalItem : Type
  CanonicalItem = Item CanonicalAstPhase

  public export
  ResolvedItem : Type
  ResolvedItem = Item ResolvedAstPhase

  public export
  TypedItem : Type
  TypedItem = Item TypedAstPhase

  -- The knots: written types and contract clauses with full expressions (at
  -- the same phase) in their expression positions.
  public export
  SurfaceTy : Type
  SurfaceTy = Ty SurfaceAstPhase SurfaceExpr

  public export
  CanonicalTy : Type
  CanonicalTy = Ty CanonicalAstPhase CanonicalExpr

  public export
  ResolvedTy : Type
  ResolvedTy = Ty ResolvedAstPhase ResolvedExpr

  public export
  TypedTy : Type
  TypedTy = Ty TypedAstPhase TypedExpr

  public export
  SurfaceContractClause : Type
  SurfaceContractClause = ContractClause SurfaceAstPhase SurfaceExpr

  public export
  CanonicalContractClause : Type
  CanonicalContractClause = ContractClause CanonicalAstPhase CanonicalExpr

  public export
  ResolvedContractClause : Type
  ResolvedContractClause = ContractClause ResolvedAstPhase ResolvedExpr

  public export
  TypedContractClause : Type
  TypedContractClause = ContractClause TypedAstPhase TypedExpr

  ------------------------------------------------------------------------------
  -- Source file
  ------------------------------------------------------------------------------

  -- One parsed SOURCE FILE -- deliberately not called "program". A Leaf
  -- program is a tree of files stitched together by `mod name;` external
  -- module declarations; the parser only ever produces one file's worth of
  -- items. The assembled whole-program structure (crate/compilation unit,
  -- one SurfaceSourceFile per file) belongs to the module loader outside
  -- the Syntax namespace, which is also where whole-program checks such as
  -- "exactly one main at the root" live -- a lone file with zero mains is a
  -- perfectly good library module and must parse.
  --
  -- Inner docs (//! and /*! ... */ at the top of the file) document the
  -- file/module itself.
  public export
  record SourceFileNode (phase : AstPhase) where
    constructor MkSourceFileNode
    sourceFileInnerDocs : List (DocComment phase)
    sourceFileItems     : List (Item phase)

  ------------------------------------------------------------------------------
  -- Items
  ------------------------------------------------------------------------------
  -- Top-level code consists of items; `let i = 1;` at top level is a parse
  -- error, which this family encodes by simply having no statement arm.

  public export
  data ItemNode : (phase : AstPhase) -> Type where
    ItemModule   : (moduleDeclaration   : ModuleDeclarationNode phase)   -> ItemNode phase -- module declaration
    ItemUse      : (useDeclaration      : UseDeclarationNode phase)      -> ItemNode phase -- use statement
    ItemConst    : (constDeclaration    : ConstDeclarationNode phase)    -> ItemNode phase -- const declaration
    ItemEnum     : (enumDeclaration     : EnumDeclarationNode phase)     -> ItemNode phase -- enum declaration
    ItemQEnum    : (qenumDeclaration    : QEnumDeclarationNode phase)    -> ItemNode phase -- qenum declaration
    ItemStruct   : (structDeclaration   : StructDeclarationNode phase)   -> ItemNode phase -- struct declaration
    ItemImpl     : (implDeclaration     : ImplDeclarationNode phase)     -> ItemNode phase -- impl block declaration
    ItemFunction : (functionDeclaration : FunctionDeclarationNode phase) -> ItemNode phase -- function declaration

  ------------------------------------------------------------------------------
  -- Function declarations
  ------------------------------------------------------------------------------

  public export
  record FunctionDeclarationNode (phase : AstPhase) where
    constructor MkFunctionDeclarationNode
    functionDocs       : List (DocComment phase)
    functionAttributes : List (Attribute phase)
    functionVisibility : Maybe (AstNode phase VisibilityQualifier)
    functionConstness  : Maybe (AstNode phase FunctionConstness)
    functionEffect     : Maybe (AstNode phase FunctionEffect)
    functionName       : Name phase
    functionParameters : List (AstNode phase (FunctionParameterNode phase))
    returnType         : Maybe (Ty phase (Expr phase))
    supportClause      : List (AstNode phase SupportKind)
    contractClauses    : List (ContractClause phase (Expr phase))
    functionBody       : Block phase

  -- Declaration-side parameters. Two shapes:
  --
  --   fn f(mut x: i32, person: &Person)   -- typed name binders
  --   fn is_adult(&self) -> bool          -- method receiver
  --
  public export
  data FunctionParameterNode : (phase : AstPhase) -> Type where

    -- Normal parameters require both a name and a type. After resolution an
    -- immutable name may target a constant pattern rather than a new parameter
    -- binding; its symbol kind and PatternReference record distinguish it.
    NormalParameter :
         (parameterDocs       : List (DocComment phase))
      -> (parameterMutability : Maybe (AstNode phase Mutability))
      -> (parameterName       : Name phase)
      -> (parameterType       : Ty phase (Expr phase))
      -> FunctionParameterNode phase

    -- `self`, `&self`, `&mut self`. Nothing = plain `self` (by value)
    ReceiverParameter :
         (receiverDocs   : List (DocComment phase))
      -> (receiverBorrow : Maybe (AstNode phase BorrowKind))
      -> FunctionParameterNode phase

  ------------------------------------------------------------------------------
  -- Struct / enum / qenum declarations
  ------------------------------------------------------------------------------

  public export
  record StructDeclarationNode (phase : AstPhase) where
    constructor MkStructDeclarationNode
    structDocs       : List (DocComment phase)
    structAttributes : List (Attribute phase)
    structVisibility : Maybe (AstNode phase VisibilityQualifier)
    structName       : Name phase
    structFields     : List (AstNode phase (StructFieldNode phase))

  -- One named field: `x: f64`. (No per-field visibility: the spec never
  -- writes `pub` on fields; parser rejection pending a ruling.)
  public export
  record StructFieldNode (phase : AstPhase) where
    constructor MkStructFieldNode
    fieldDocs : List (DocComment phase)
    fieldName : Name phase
    fieldType : Ty phase (Expr phase)

  public export
  record EnumDeclarationNode (phase : AstPhase) where
    constructor MkEnumDeclarationNode
    enumDocs       : List (DocComment phase)
    enumAttributes : List (Attribute phase)
    enumVisibility : Maybe (AstNode phase VisibilityQualifier)
    enumName       : Name phase
    enumVariants   : List (AstNode phase (EnumVariantNode phase))

  -- Classical enum variants mix freely within one enum:
  --   Zero,                      -- unit-like
  --   Left(i32),                 -- tuple-like (>= 1 payload type)
  --   Move { x: i32, y: i32 },   -- struct-like
  public export
  record EnumVariantNode (phase : AstPhase) where
    constructor MkEnumVariantNode
    variantDocs : List (DocComment phase)
    variantName : Name phase
    variantBody : EnumVariantBody phase

  public export
  data EnumVariantBody : (phase : AstPhase) -> Type where
    VariantUnit   : EnumVariantBody phase
    VariantTuple  : (payloadTypes  : List1 (Ty phase (Expr phase))) -> EnumVariantBody phase
    VariantStruct : (payloadFields : List (AstNode phase (StructFieldNode phase)))
                 -> EnumVariantBody phase

  -- qenum: ONLY tuple-like variants exist, which the AST enforces by
  -- construction -- there is no unit or struct arm to build.
  public export
  record QEnumDeclarationNode (phase : AstPhase) where
    constructor MkQEnumDeclarationNode
    qenumDocs       : List (DocComment phase)
    qenumAttributes : List (Attribute phase)
    qenumVisibility : Maybe (AstNode phase VisibilityQualifier)
    qenumName       : Name phase
    qenumVariants   : List (AstNode phase (QEnumVariantNode phase))

  public export
  record QEnumVariantNode (phase : AstPhase) where
    constructor MkQEnumVariantNode
    qenumVariantDocs         : List (DocComment phase)
    qenumVariantName         : Name phase
    qenumVariantPayloadTypes : List1 (Ty phase (Expr phase))

  ------------------------------------------------------------------------------
  -- impl / const / use / mod declarations
  ------------------------------------------------------------------------------

  -- `impl Person { fn new(...) -> Person { ... } ... }`. Only function
  -- declarations occur inside impl blocks per the spec.
  public export
  record ImplDeclarationNode (phase : AstPhase) where
    constructor MkImplDeclarationNode
    implDocs      : List (DocComment phase)
    implTarget    : Path phase
    implFunctions : List (AstNode phase (FunctionDeclarationNode phase))

  -- `const FIVE: i32 = 5;`. The type annotation is MANDATORY on consts
  -- (as in Rust; the spec always writes it).
  public export
  record ConstDeclarationNode (phase : AstPhase) where
    constructor MkConstDeclarationNode
    constDocs       : List (DocComment phase)
    constVisibility : Maybe (AstNode phase VisibilityQualifier)
    constName       : Name phase
    constType       : Ty phase (Expr phase)
    constValue      : Expr phase

  -- `use my_library::helper;` or `use my_library::helper as help;`
  public export
  record UseDeclarationNode (phase : AstPhase) where
    constructor MkUseDeclarationNode
    useDocs       : List (DocComment phase)
    useVisibility : Maybe (AstNode phase VisibilityQualifier)
    usePath       : Path phase
    useAlias      : Maybe (AstNode phase NameNode)

  -- Two source forms:
  --   mod my_module { ...items... }   -- inline body
  --   mod my_library;                 -- external file
  public export
  record ModuleDeclarationNode (phase : AstPhase) where
    constructor MkModuleDeclarationNode
    moduleDocs       : List (DocComment phase)
    moduleVisibility : Maybe (AstNode phase VisibilityQualifier)
    moduleName       : Name phase
    moduleBody       : ModuleBody phase

  public export
  data ModuleBody : (phase : AstPhase) -> Type where
    ModuleInline :
         (moduleInnerDocs : List (DocComment phase))
      -> (moduleItems     : List (Item phase))
      -> ModuleBody phase
    ModuleExternal :
         ModuleBody phase

  ------------------------------------------------------------------------------
  -- Blocks
  ------------------------------------------------------------------------------

  -- Rust-style semicolon rules, preserved structurally: statements end in
  -- `;` (or are block-like), and the optional trailing expression WITHOUT
  -- `;` is the block's value.
  public export
  record BlockNode (phase : AstPhase) where
    constructor MkBlockNode
    blockInnerDocs  : List (DocComment phase)
    blockStatements : List (Statement phase)
    finalExpression : Maybe (Expr phase)

  ------------------------------------------------------------------------------
  -- Statements
  ------------------------------------------------------------------------------

  public export
  data StatementNode : (phase : AstPhase) -> Type where

    StatementLet :
         (letBinding : LetBindingNode phase)
      -> StatementNode phase

    StatementAssignment :
         (assignment : AssignmentNode phase)
      -> StatementNode phase

    -- An expression statement WITH a written `;`:  f(&q);  x + 1;
    StatementSemiExpression :
         (statementExpression : Expr phase)
      -> StatementNode phase

    -- A block-like expression in statement position WITHOUT `;`, in
    -- non-final position:  if c { ... } else { ... }  loop { ... }
    -- Distinct from StatementSemiExpression so "expected `;`" diagnostics
    -- and pretty-printing see what was written.
    StatementExpression :
         (statementExpression : Expr phase)
      -> StatementNode phase

  -- let [qualifiers] pattern [: Ty] [= | := expr] ;
  --
  -- The initializer bundles the marker WITH the expression, so
  -- "marker without initializer" is unrepresentable; `let a: [i32; 4];`
  -- (no initializer at all) is Nothing.
  public export
  record LetBindingNode (phase : AstPhase) where
    constructor MkLetBindingNode
    -- Source order; empty = none written. `let scratch linear q = ...`.
    letQualifiers    : List (AstNode phase QuantumStorageQualifier)
    letPattern       : Pattern phase
    letTypeAnnotation : Maybe (Ty phase (Expr phase))
    letInitializer   : Maybe (LetInitializerNode phase)

  public export
  record LetInitializerNode (phase : AstPhase) where
    constructor MkLetInitializerNode
    -- the `:=` span is what "auto-uncompute is not allowed on
    -- classical bindings"-style diagnostics point at.
    initializerMarker : AstNode phase InitializerMarker
    initializerValue  : Expr phase

  -- target op value;  where op is =, +=, <<=, ... (never :=).
  public export
  record AssignmentNode (phase : AstPhase) where
    constructor MkAssignmentNode
    assignmentTarget   : AstNode phase (AssignmentTargetNode phase)
    assignmentOperator : AstNode phase AssignmentOperator
    assignmentValue    : Expr phase

  -- The assignable-place grammar, kept apart from general expressions:
  --   x = 5;   x[0] = 10;   p.x = v;   t.0 = 3;
  -- Base positions are expressions (qs[i].0 = ... nests), but the OUTER
  -- shape is one of exactly these four; `f() = 5;` is unrepresentable.
  public export
  data AssignmentTargetNode : (phase : AstPhase) -> Type where

    AssignTargetName :
         (targetName : Name phase)
      -> AssignmentTargetNode phase

    AssignTargetIndex :
         (targetObject    : Expr phase)
      -> (indexExpression : Expr phase)
      -> AssignmentTargetNode phase

    AssignTargetField :
         (targetObject : Expr phase)
      -> (fieldName    : MemberName phase)
      -> AssignmentTargetNode phase

    -- t.0 = 3;  index spelling preserved raw, like every numeric literal.
    AssignTargetTupleIndex :
         (targetObject      : Expr phase)
      -> (tupleIndexRawText : String)
      -> AssignmentTargetNode phase

  ------------------------------------------------------------------------------
  -- Expressions
  ------------------------------------------------------------------------------

  public export
  data ExpressionNode : (phase : AstPhase) -> Type where

    ExprLiteral :
         (literal : Literal phase)
      -> ExpressionNode phase

    -- A lone identifier. PARSER RULE (mirroring PatternName/PatternPath):
    -- one segment => ExprName, multiple segments => ExprPath.
    ExprName :
         (valueName : Name phase)
      -> ExpressionNode phase

    -- Data::Left, Person::new, my_library::helper -- what the path denotes
    -- (variant, associated function, imported item) is resolution's job.
    ExprPath :
         (valuePath : Path phase)
      -> ExpressionNode phase

    -- A non-shadowable builtin in expression (usually callee) position:
    -- qalloc, measr, reset, discard, uncompute, weaken, barrier, ...
    -- These are ordinary calls -- ExprCall (ExprBuiltin BuiltinMeasr) [q] --
    -- with NO dedicated per-builtin nodes; only ctrl/adjoint have real
    -- grammar of their own (below).
    ExprBuiltin :
         (builtinFunction : Builtin)
      -> ExpressionNode phase

    -- `self` in method bodies. Carries the resolved SymbolId of the
    -- enclosing receiver parameter from ResolvedAstPhase onward, exactly as
    -- NameFor does for ExprName/ExprPath -- see SelfFor in Name.idr.
    ExprSelf :
         (selfReceiver : SelfFor phase)
      -> ExpressionNode phase

    -- (e) -- kept distinct from (e,) [one-element ExprTuple]; discarded at
    -- canonicalization. Same story as TyParenthesized/PatternParenthesized.
    ExprParenthesized :
         (innerExpression : Expr phase)
      -> ExpressionNode phase

    -- (a, b), (e,). At least one element; `()` is ExprLiteral LiteralUnit.
    ExprTuple :
         (tupleElements : List1 (Expr phase))
      -> ExpressionNode phase

    -- [1, 2, 3]; [] is legal syntax (typed elsewhere).
    ExprArray :
         (arrayElements : List (Expr phase))
      -> ExpressionNode phase

    -- [0; 3] -- element repeated count times; count is const-checked later.
    ExprRepeatedArray :
         (repeatedElement : Expr phase)
      -> (repeatCount     : Expr phase)
      -> ExpressionNode phase

    -- Point { x: 1.0, y: 2.0 } / Pair { q0, q1 } -- shorthand vs explicit
    -- preserved per field.
    ExprStructLiteral :
         (structPath        : Path phase)
      -> (fieldInitializers : List (AstNode phase (FieldInitializerNode phase)))
      -> ExpressionNode phase

    -- f(a, b) -- callee is a full expression: names, paths, builtins,
    -- adjoint(f), ctrl(...).apply(f), parenthesized expressions.
    ExprCall :
         (callee        : Expr phase)
      -> (callArguments : List (Expr phase))
      -> ExpressionNode phase

    -- a.len(), sq1.tensor(sq2), (0..n).rev(). The method name is stored
    -- textually even when it arrives as a builtin token (`tensor`): its
    -- category is recoverable via builtinFromString, and method-position
    -- resolution is a later concern.
    ExprMethodCall :
         (receiver        : Expr phase)
      -> (methodName      : MemberName phase)
      -> (methodArguments : List (Expr phase))
      -> ExpressionNode phase

    -- p.x
    ExprField :
         (fieldObject : Expr phase)
      -> (fieldName   : MemberName phase)
      -> ExpressionNode phase

    -- t.0 -- raw index spelling preserved.
    ExprTupleIndex :
         (indexedTuple      : Expr phase)
      -> (tupleIndexRawText : String)
      -> ExpressionNode phase

    -- a[i], and also slicing: a[1..4] is ExprIndex with a range index --
    -- slicing is not a separate node, exactly as in Rust's AST. `&a[1..4]`
    -- is ExprUnary borrow around this.
    ExprIndex :
         (indexedObject   : Expr phase)
      -> (indexExpression : Expr phase)
      -> ExpressionNode phase

    -- Operators are located so "cannot apply `+` here" points at the `+`.
    ExprUnary :
         (unaryOperator : AstNode phase UnaryOperator)
      -> (operand       : Expr phase)
      -> ExpressionNode phase

    ExprBinary :
         (binaryOperator : AstNode phase BinaryOperator)
      -> (leftOperand    : Expr phase)
      -> (rightOperand   : Expr phase)
      -> ExpressionNode phase

    -- a..b, a.., ..=5, .. -- both endpoints optional; `a..=` (inclusive
    -- with no end) is a parser rejection, not an AST impossibility.
    ExprRange :
         (rangeStart    : Maybe (Expr phase))
      -> (rangeOperator : AstNode phase RangeOperator)
      -> (rangeEnd      : Maybe (Expr phase))
      -> ExpressionNode phase

    -- e as T
    ExprCast :
         (castOperand : Expr phase)
      -> (castTarget  : Ty phase (Expr phase))
      -> ExpressionNode phase

    ExprBlock :
         (blockExpression : Block phase)
      -> ExpressionNode phase

    ExprIf :
         (ifExpression : ClassicalIfNode phase)
      -> ExpressionNode phase

    ExprQIf :
         (qifExpression : QuantumIfNode phase)
      -> ExpressionNode phase

    ExprSIf :
         (sifExpression : StateIfNode phase)
      -> ExpressionNode phase

    ExprMatch :
         (matchExpression : ClassicalMatchNode phase)
      -> ExpressionNode phase

    ExprQMatch :
         (qmatchExpression : QuantumMatchNode phase)
      -> ExpressionNode phase

    ExprSMatch :
         (smatchExpression : StateMatchNode phase)
      -> ExpressionNode phase

    ExprLoop :
         (loopBody : Block phase)
      -> ExpressionNode phase

    ExprWhile :
         (whileCondition : Expr phase)
      -> (whileBody      : Block phase)
      -> ExpressionNode phase

    -- for i in 1..6 { ... } -- the binder is a full pattern
    -- (for (a, b) in ... is representable; a ruling can restrict it).
    ExprFor :
         (forPattern       : Pattern phase)
      -> (forIterExpression : Expr phase)
      -> (forBody          : Block phase)
      -> ExpressionNode phase

    ExprBreak :
         (breakValue : Maybe (Expr phase))
      -> ExpressionNode phase

    ExprContinue :
         ExpressionNode phase

    ExprReturn :
         (returnValue : Maybe (Expr phase))
      -> ExpressionNode phase

    ExprCtrl :
         (controlExpression : ControlExpressionNode phase)
      -> ExpressionNode phase

    ExprAdjoint :
         (adjointExpression : AdjointExpressionNode phase)
      -> ExpressionNode phase

  -- One field in a struct literal: Pair { q0, q1 } vs Point { x: 1.0 }.
  public export
  data FieldInitializerNode : (phase : AstPhase) -> Type where

    FieldInitShorthand :
         (fieldAndValueName : Name phase)
      -> FieldInitializerNode phase

    FieldInitExplicit :
         (fieldName  : Name phase)
      -> (fieldValue : Expr phase)
      -> FieldInitializerNode phase

  ------------------------------------------------------------------------------
  -- if / qif / sif
  ------------------------------------------------------------------------------

  -- if cond { ... } [else { ... } | else if ...]
  -- Branches are blocks; else-if chains nest through ElseChainedIf,
  -- so else associates with the nearest unmatched if
  public export
  record ClassicalIfNode (phase : AstPhase) where
    constructor MkClassicalIfNode
    ifCondition  : Expr phase
    ifThenBlock  : Block phase
    ifElseBranch : Maybe (ClassicalElseNode phase)

  public export
  data ClassicalElseNode : (phase : AstPhase) -> Type where
    ElseBlock     : (elseBlock : Block phase) -> ClassicalElseNode phase
    ElseChainedIf : (chainedIf : AstNode phase (ClassicalIfNode phase)) -> ClassicalElseNode phase

  -- qif cond { ... } [qelse { ... }]      -- block branches
  -- qif c e1 qelse e2                     -- bare expression branches
  -- qelse optional
  public export
  record QuantumIfNode (phase : AstPhase) where
    constructor MkQuantumIfNode
    qifCondition  : Expr phase
    qifThenBranch : QuantumBranchNode phase
    qifElseBranch : Maybe (QuantumBranchNode phase)

  public export
  data QuantumBranchNode : (phase : AstPhase) -> Type where
    QuantumBranchBlock      : (branchBlock : Block phase) -> QuantumBranchNode phase
    QuantumBranchExpression : (branchExpression : Expr phase) -> QuantumBranchNode phase

  -- sif cond then e1 selse e2 -- expression-only,
  -- selse mandatory, `then` keyword required
  public export
  record StateIfNode (phase : AstPhase) where
    constructor MkStateIfNode
    sifCondition      : Expr phase
    sifThenExpression : Expr phase
    sifElseExpression : Expr phase

  ------------------------------------------------------------------------------
  -- match / qmatch / smatch -- three families
  ------------------------------------------------------------------------------

  public export
  record ClassicalMatchNode (phase : AstPhase) where
    constructor MkClassicalMatchNode
    matchScrutinee : Expr phase
    matchArms      : List (AstNode phase (ClassicalMatchArmNode phase))

  -- pattern [if guard] => body   -- the guard lives on the ARM (it
  -- conditions the arm, it is not part of the pattern), which is also what
  -- keeps Pattern.idr independent of expressions.
  public export
  record ClassicalMatchArmNode (phase : AstPhase) where
    constructor MkClassicalMatchArmNode
    armPattern : Pattern phase
    armGuard   : Maybe (Expr phase)
    armBody    : Expr phase

  public export
  record QuantumMatchNode (phase : AstPhase) where
    constructor MkQuantumMatchNode
    qmatchScrutinee : Expr phase
    qmatchArms      : List (AstNode phase (QuantumMatchArmNode phase))

  public export
  record StateMatchNode (phase : AstPhase) where
    constructor MkStateMatchNode
    smatchScrutinee : Expr phase
    smatchArms      : List (AstNode phase (QuantumMatchArmNode phase))

  -- Shared by qmatch and smatch: the pattern grammar is the shared
  -- QuantumMatchPatternNode (Pattern.idr), with smatch's restrictions
  -- (no wildcard, no qenum variants) enforced at parse time. No guards in
  -- quantum matches -- the spec has none, so the field does not exist.
  public export
  record QuantumMatchArmNode (phase : AstPhase) where
    constructor MkQuantumMatchArmNode
    quantumArmPattern : QuantumMatchPattern phase
    quantumArmBody    : Expr phase

  ------------------------------------------------------------------------------
  -- ctrl and adjoint -- the two builtins with genuine grammar
  ------------------------------------------------------------------------------

  -- Both are modeled as CALLABLE-PRODUCING expressions plus a block form.
  -- Application is ordinary ExprCall around them:
  --
  --   adjoint(f)(q1, q2)      = ExprCall (ExprAdjoint (AdjointOfCallable f)) [q1, q2]
  --   let g = adjoint(f);     = ExprAdjoint (AdjointOfCallable f)   -- no call
  --   ctrl(c).apply(H)(&q2)   = ExprCall (ExprCtrl (ControlledCallable ...)) [&q2]
  --
  -- This shape exists because `adjoint(f)` IS a first-class value in the
  -- spec ("adjoint as higher order function"); bundling target arguments
  -- into the node, as a plainer design would, cannot represent the uncalled
  -- form without an empty-argument hack.

  public export
  data ControlExpressionNode : (phase : AstPhase) -> Type where

    -- ctrl(c0, c1)[.on(bs"10")].apply(f) -- at least one control; the
    -- optional basis string is preserved raw (bs"10" as written).
    ControlledCallable :
         (controlQbits  : List1 (Expr phase))
      -> (onBasisRaw     : Maybe (AstNode phase String))
      -> (controlledCallable : Expr phase)
      -> ControlExpressionNode phase

    -- ctrl(c0, c1)[.on(bs"10")] { ...body... }
    ControlledBlock :
         (controlQbits   : List1 (Expr phase))
      -> (onBasisRaw      : Maybe (AstNode phase String))
      -> (controlledBlock : Block phase)
      -> ControlExpressionNode phase

  public export
  data AdjointExpressionNode : (phase : AstPhase) -> Type where

    -- adjoint(f) -- a first-class callable value.
    AdjointOfCallable :
         (adjointedCallable : Expr phase)
      -> AdjointExpressionNode phase

    -- adjoint { ...body... }
    AdjointBlock :
         (adjointedBlock : Block phase)
      -> AdjointExpressionNode phase

--------------------------------------------------------------------------------
-- Remaining located aliases
--------------------------------------------------------------------------------

public export
SourceFile : AstPhase -> Type
SourceFile phase = AstNode phase (SourceFileNode phase)

public export
SurfaceSourceFile : Type
SurfaceSourceFile = SourceFile SurfaceAstPhase

public export
CanonicalSourceFile : Type
CanonicalSourceFile = SourceFile CanonicalAstPhase

public export
ResolvedSourceFile : Type
ResolvedSourceFile = SourceFile ResolvedAstPhase

public export
TypedSourceFile : Type
TypedSourceFile = SourceFile TypedAstPhase

public export
FunctionDeclaration : AstPhase -> Type
FunctionDeclaration phase = AstNode phase (FunctionDeclarationNode phase)

public export
SurfaceFunctionDeclaration : Type
SurfaceFunctionDeclaration = FunctionDeclaration SurfaceAstPhase

public export
CanonicalFunctionDeclaration : Type
CanonicalFunctionDeclaration = FunctionDeclaration CanonicalAstPhase

public export
ResolvedFunctionDeclaration : Type
ResolvedFunctionDeclaration = FunctionDeclaration ResolvedAstPhase

public export
TypedFunctionDeclaration : Type
TypedFunctionDeclaration = FunctionDeclaration TypedAstPhase

public export
FunctionParameter : AstPhase -> Type
FunctionParameter phase = AstNode phase (FunctionParameterNode phase)

public export
SurfaceFunctionParameter : Type
SurfaceFunctionParameter = FunctionParameter SurfaceAstPhase

public export
CanonicalFunctionParameter : Type
CanonicalFunctionParameter = FunctionParameter CanonicalAstPhase

public export
ResolvedFunctionParameter : Type
ResolvedFunctionParameter = FunctionParameter ResolvedAstPhase

public export
TypedFunctionParameter : Type
TypedFunctionParameter = FunctionParameter TypedAstPhase

public export
StructDeclaration : AstPhase -> Type
StructDeclaration phase = AstNode phase (StructDeclarationNode phase)

public export
SurfaceStructDeclaration : Type
SurfaceStructDeclaration = StructDeclaration SurfaceAstPhase

public export
CanonicalStructDeclaration : Type
CanonicalStructDeclaration = StructDeclaration CanonicalAstPhase

public export
ResolvedStructDeclaration : Type
ResolvedStructDeclaration = StructDeclaration ResolvedAstPhase

public export
TypedStructDeclaration : Type
TypedStructDeclaration = StructDeclaration TypedAstPhase

public export
EnumDeclaration : AstPhase -> Type
EnumDeclaration phase = AstNode phase (EnumDeclarationNode phase)

public export
SurfaceEnumDeclaration : Type
SurfaceEnumDeclaration = EnumDeclaration SurfaceAstPhase

public export
CanonicalEnumDeclaration : Type
CanonicalEnumDeclaration = EnumDeclaration CanonicalAstPhase

public export
ResolvedEnumDeclaration : Type
ResolvedEnumDeclaration = EnumDeclaration ResolvedAstPhase

public export
TypedEnumDeclaration : Type
TypedEnumDeclaration = EnumDeclaration TypedAstPhase

public export
QEnumDeclaration : AstPhase -> Type
QEnumDeclaration phase = AstNode phase (QEnumDeclarationNode phase)

public export
SurfaceQEnumDeclaration : Type
SurfaceQEnumDeclaration = QEnumDeclaration SurfaceAstPhase

public export
CanonicalQEnumDeclaration : Type
CanonicalQEnumDeclaration = QEnumDeclaration CanonicalAstPhase

public export
ResolvedQEnumDeclaration : Type
ResolvedQEnumDeclaration = QEnumDeclaration ResolvedAstPhase

public export
TypedQEnumDeclaration : Type
TypedQEnumDeclaration = QEnumDeclaration TypedAstPhase

public export
ImplDeclaration : AstPhase -> Type
ImplDeclaration phase = AstNode phase (ImplDeclarationNode phase)

public export
SurfaceImplDeclaration : Type
SurfaceImplDeclaration = ImplDeclaration SurfaceAstPhase

public export
CanonicalImplDeclaration : Type
CanonicalImplDeclaration = ImplDeclaration CanonicalAstPhase

public export
ResolvedImplDeclaration : Type
ResolvedImplDeclaration = ImplDeclaration ResolvedAstPhase

public export
TypedImplDeclaration : Type
TypedImplDeclaration = ImplDeclaration TypedAstPhase

public export
ConstDeclaration : AstPhase -> Type
ConstDeclaration phase = AstNode phase (ConstDeclarationNode phase)

public export
SurfaceConstDeclaration : Type
SurfaceConstDeclaration = ConstDeclaration SurfaceAstPhase

public export
CanonicalConstDeclaration : Type
CanonicalConstDeclaration = ConstDeclaration CanonicalAstPhase

public export
ResolvedConstDeclaration : Type
ResolvedConstDeclaration = ConstDeclaration ResolvedAstPhase

public export
TypedConstDeclaration : Type
TypedConstDeclaration = ConstDeclaration TypedAstPhase

public export
UseDeclaration : AstPhase -> Type
UseDeclaration phase = AstNode phase (UseDeclarationNode phase)

public export
SurfaceUseDeclaration : Type
SurfaceUseDeclaration = UseDeclaration SurfaceAstPhase

public export
CanonicalUseDeclaration : Type
CanonicalUseDeclaration = UseDeclaration CanonicalAstPhase

public export
ResolvedUseDeclaration : Type
ResolvedUseDeclaration = UseDeclaration ResolvedAstPhase

public export
TypedUseDeclaration : Type
TypedUseDeclaration = UseDeclaration TypedAstPhase

public export
ModuleDeclaration : AstPhase -> Type
ModuleDeclaration phase = AstNode phase (ModuleDeclarationNode phase)

public export
SurfaceModuleDeclaration : Type
SurfaceModuleDeclaration = ModuleDeclaration SurfaceAstPhase

public export
CanonicalModuleDeclaration : Type
CanonicalModuleDeclaration = ModuleDeclaration CanonicalAstPhase

public export
ResolvedModuleDeclaration : Type
ResolvedModuleDeclaration = ModuleDeclaration ResolvedAstPhase

public export
TypedModuleDeclaration : Type
TypedModuleDeclaration = ModuleDeclaration TypedAstPhase

public export
LetBinding : AstPhase -> Type
LetBinding phase = AstNode phase (LetBindingNode phase)

public export
SurfaceLetBinding : Type
SurfaceLetBinding = LetBinding SurfaceAstPhase

public export
CanonicalLetBinding : Type
CanonicalLetBinding = LetBinding CanonicalAstPhase

public export
ResolvedLetBinding : Type
ResolvedLetBinding = LetBinding ResolvedAstPhase

public export
TypedLetBinding : Type
TypedLetBinding = LetBinding TypedAstPhase

public export
AssignmentTarget : AstPhase -> Type
AssignmentTarget phase = AstNode phase (AssignmentTargetNode phase)

public export
SurfaceAssignmentTarget : Type
SurfaceAssignmentTarget = AssignmentTarget SurfaceAstPhase

public export
CanonicalAssignmentTarget : Type
CanonicalAssignmentTarget = AssignmentTarget CanonicalAstPhase

public export
ResolvedAssignmentTarget : Type
ResolvedAssignmentTarget = AssignmentTarget ResolvedAstPhase

public export
TypedAssignmentTarget : Type
TypedAssignmentTarget = AssignmentTarget TypedAstPhase

public export
ClassicalMatchArm : AstPhase -> Type
ClassicalMatchArm phase = AstNode phase (ClassicalMatchArmNode phase)

public export
SurfaceClassicalMatchArm : Type
SurfaceClassicalMatchArm = ClassicalMatchArm SurfaceAstPhase

public export
CanonicalClassicalMatchArm : Type
CanonicalClassicalMatchArm = ClassicalMatchArm CanonicalAstPhase

public export
ResolvedClassicalMatchArm : Type
ResolvedClassicalMatchArm = ClassicalMatchArm ResolvedAstPhase

public export
TypedClassicalMatchArm : Type
TypedClassicalMatchArm = ClassicalMatchArm TypedAstPhase

public export
QuantumMatchArm : AstPhase -> Type
QuantumMatchArm phase = AstNode phase (QuantumMatchArmNode phase)

public export
SurfaceQuantumMatchArm : Type
SurfaceQuantumMatchArm = QuantumMatchArm SurfaceAstPhase

public export
CanonicalQuantumMatchArm : Type
CanonicalQuantumMatchArm = QuantumMatchArm CanonicalAstPhase

public export
ResolvedQuantumMatchArm : Type
ResolvedQuantumMatchArm = QuantumMatchArm ResolvedAstPhase

public export
TypedQuantumMatchArm : Type
TypedQuantumMatchArm = QuantumMatchArm TypedAstPhase

public export
SurfaceContractPredicate : Type
SurfaceContractPredicate = ContractPredicate SurfaceAstPhase SurfaceExpr

public export
CanonicalContractPredicate : Type
CanonicalContractPredicate = ContractPredicate CanonicalAstPhase CanonicalExpr

public export
ResolvedContractPredicate : Type
ResolvedContractPredicate = ContractPredicate ResolvedAstPhase ResolvedExpr

public export
TypedContractPredicate : Type
TypedContractPredicate = ContractPredicate TypedAstPhase TypedExpr
