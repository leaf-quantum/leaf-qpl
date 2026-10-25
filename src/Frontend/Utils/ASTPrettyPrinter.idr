module Frontend.Utils.ASTPrettyPrinter

import Data.List1

import Frontend.Token
import Frontend.ASTPhases
import Frontend.Syntax.AST
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
-- Pretty-printing for the AST (Frontend.Syntax.AST and friends).
--------------------------------------------------------------------------------
-- Two styles, selected by PrettyStyle:
--
--   PrettyLax    (default) -- parentheses are printed only where the source
--                              would otherwise re-parse differently, i.e. the
--                              usual "minimal parenthesization" pretty-printer
--   PrettyStrict            -- every syntactically OPTIONAL parenthesis
--                              (around unary/binary/cast/range operands) is
--                              printed explicitly, regardless of precedence
--
-- Both styles still print MANDATORY parentheses -- e.g. around a block-like
-- expression (if/match/loop/...) used as the base of a postfix operation --
-- since those are not "optional", they are required for the output to
-- re-parse to the same tree.
--
-- TOTALITY: this module follows the discipline documented at the top of
-- Compiler.Validation.PostParseValidation ("learned the hard way"): Idris 2's size-change checker
-- credits CONSTRUCTOR PATTERNS ONLY. Every record is destructured via its
-- constructor in the pattern head (never through a `.field` projection) when
-- the projected value feeds a recursive call, and every List/List1 that is
-- walked with a function from the same recursive group is walked with a
-- hand-written recursive helper (never `map`/`concatMap`/`maybe`, which hide
-- the recursive call behind a higher-order function the checker cannot see
-- through). Expressions and types are mutually recursive (casts embed types,
-- array-size positions embed expressions), while blocks and statements close
-- that recursive core. Downstream declaration printers are kept in smaller
-- groups; modules and items form a second genuine recursive group. One
-- `assert_total` boundary breaks the otherwise global cycle while keeping
-- every printer entry point total.
--
-- Patterns (Frontend.Syntax.Pattern) do not depend on expressions, so they
-- get their own, smaller mutual block, checked independently and reused
-- freely (via ordinary, non-recursive calls) from the core block below.
--
-- PHASE POLYMORPHISM: every renderer is generic over `phase : AstPhase`
-- ("trees that grow": surface -> canonical -> resolved -> typed). The ONLY
-- payloads that differ across phases are names, member names and paths --
-- `NameFor phase` (a bare `NameNode` until resolution attaches a `SymbolId`),
-- `MemberNameFor phase` (a bare `NameNode` until typechecking) and
-- `PathFor phase` (a segment list until resolution collapses it). Those three
-- are the whole content of the `PhasePretty` interface below; the rendered
-- form is always just the written text (a pretty-printer reproduces source
-- syntax, so a resolved name's `SymbolId` is intentionally dropped).
-- Everything else in the AST is uniformly phase-parametric, so the bodies
-- are shared verbatim by all four phases.
--------------------------------------------------------------------------------

public export
data PrettyStyle
  = PrettyLax
  | PrettyStrict

isPrettyStrict : PrettyStyle -> Bool
isPrettyStrict PrettyStrict = True
isPrettyStrict PrettyLax    = False

--------------------------------------------------------------------------------
-- Generic string helpers
--------------------------------------------------------------------------------

joinWith : String -> List String -> String
joinWith _   []        = ""
joinWith _   [x]       = x
joinWith sep (x :: xs) = x ++ sep ++ joinWith sep xs

parens : String -> String
parens s = "(" ++ s ++ ")"

brackets : String -> String
brackets s = "[" ++ s ++ "]"

braces : String -> String
braces s = "{ " ++ s ++ " }"

-- "" stays "", anything else gets a trailing space -- for optional keyword
-- prefixes such as `pub `/`mut ` whose Show instance prints "" when absent.
prefixSpace : String -> String
prefixSpace ""  = ""
prefixSpace str = str ++ " "

showBoolLower : Bool -> String
showBoolLower True  = "true"
showBoolLower False = "false"

-- Whether a rendered fragment starts with `&`. A bare `&` prefix (SharedBorrow,
-- no trailing space) glued directly onto a fragment that itself starts with
-- `&` would re-lex as the single `&&` token instead of two `&` tokens, so
-- callers use this to decide whether a defensive space is needed.
startsWithAmp : String -> Bool
startsWithAmp s =
  case unpack s of
    ('&' :: _) => True
    _          => False

-- `&`/`&mut` prefixed onto an already-rendered body, safe against the `&&`
-- collision above. `&mut` already carries its own trailing space (a word
-- boundary is required regardless), so only the bare `&` case needs the check.
showBorrowPrefixed : BorrowKind -> String -> String
showBorrowPrefixed SharedBorrow  body = "&" ++ (if startsWithAmp body then " " else "") ++ body
showBorrowPrefixed MutableBorrow body = "&mut " ++ body

-- (), (x,), (x, y, ...) -- the shared tuple-printing shape used by
-- expression tuples, type tuples, and pattern tuples alike.
showTupleLike : List String -> String
showTupleLike []  = "()"
showTupleLike [x] = "(" ++ x ++ ",)"
showTupleLike xs  = "(" ++ joinWith ", " xs ++ ")"

--------------------------------------------------------------------------------
-- Names and paths (Frontend.Syntax.Name)
--------------------------------------------------------------------------------
-- Path segments are phase-invariant text (`self` or an identifier), so this
-- one is a plain generic function. Names and whole paths are what the
-- `PhasePretty` interface abstracts -- see the module header.
--------------------------------------------------------------------------------

showPathSegment : PathSegment phase -> String
showPathSegment (MkAstNode _ _ seg) =
  case seg of
    PathSegmentName s => s
    PathSegmentSelf   => "self"

prettyNameNode : NameNode -> String
prettyNameNode (MkNameNode text) = text

prettyResolvedNameNode : ResolvedNameNode -> String
prettyResolvedNameNode (MkResolvedNameNode text _) = text

prettyPathNode : PathNode phase -> String
prettyPathNode (MkPathNode first rest) =
  joinWith "::" (showPathSegment first :: map showPathSegment rest)

prettyResolvedPathNode : ResolvedPathNode -> String
prettyResolvedPathNode (MkResolvedPathNode first rest _) =
  joinWith "::" (first :: rest)

-- Rendering the three payloads that "grow" across phases. The interface
-- methods take raw payloads; the located wrappers below unwrap AstNode first.
public export
interface PhasePretty phase where
  prettyName : NameFor phase -> String
  prettyMemberName : MemberNameFor phase -> String
  prettyPath : PathFor phase -> String

public export
PhasePretty SurfaceAstPhase where
  prettyName = prettyNameNode
  prettyMemberName = prettyNameNode
  prettyPath = prettyPathNode

public export
PhasePretty CanonicalAstPhase where
  prettyName = prettyNameNode
  prettyMemberName = prettyNameNode
  prettyPath = prettyPathNode

public export
PhasePretty ResolvedAstPhase where
  prettyName = prettyResolvedNameNode
  prettyMemberName = prettyNameNode
  prettyPath = prettyResolvedPathNode

public export
PhasePretty TypedAstPhase where
  prettyName = prettyResolvedNameNode
  prettyMemberName = prettyResolvedNameNode
  prettyPath = prettyResolvedPathNode

showName : PhasePretty phase => Name phase -> String
showName (MkAstNode _ _ n) = prettyName n

showMemberName : PhasePretty phase => MemberName phase -> String
showMemberName (MkAstNode _ _ n) = prettyMemberName n

showPath : PhasePretty phase => Path phase -> String
showPath (MkAstNode _ _ p) = prettyPath p

-- Attribute names and import aliases retain plain spelling at every phase,
-- so they are rendered directly, with no `PhasePretty` constraint.
showPlainName : AstNode phase NameNode -> String
showPlainName (MkAstNode _ _ (MkNameNode text)) = text

--------------------------------------------------------------------------------
-- Literals (Frontend.Syntax.Literal) -- every payload is already the raw
-- source spelling (or a value with exactly one spelling), so this is a flat
-- lookup, no recursion.
--------------------------------------------------------------------------------

showLiteral : Literal phase -> String
showLiteral (MkAstNode _ _ lit) =
  case lit of
    LiteralIntegerRaw s     => s
    LiteralFloatRaw s       => s
    LiteralStringRaw s      => s
    LiteralByteRaw s        => s
    LiteralByteStringRaw s  => s
    LiteralBasisStringRaw s => s
    LiteralBoolean b        => showBoolLower b
    LiteralUnit             => "()"
    LiteralQuantumState st  => show st

--------------------------------------------------------------------------------
-- Doc comments (Frontend.Syntax.Doc) -- the raw spelling already includes
-- delimiters, so printing one back out is verbatim.
--------------------------------------------------------------------------------

showDocComment : DocComment phase -> String
showDocComment (MkAstNode _ _ (MkDocCommentNode _ _ rawText)) = rawText

-- A block of doc comments, one per line, immediately preceding whatever
-- follows -- "" when there are none.
docsPrefix : List (DocComment phase) -> String
docsPrefix docs = concatMap (\d => showDocComment d ++ "\n") docs

--------------------------------------------------------------------------------
-- Attributes (Frontend.Syntax.Attribute)
--------------------------------------------------------------------------------

showAttributeArgument : AttributeArgument phase -> String
showAttributeArgument (MkAstNode _ _ (AttributeArgumentStringLit s)) = s

showAttribute : Attribute phase -> String
showAttribute (MkAstNode _ _ (MkAttributeNode nm margs)) =
  "#[" ++ showPlainName nm ++
    (case margs of
       Nothing   => ""
       Just args => "(" ++ joinWith ", " (map showAttributeArgument args) ++ ")") ++
  "]"

attrsPrefix : List (Attribute phase) -> String
attrsPrefix attrs = concatMap (\a => showAttribute a ++ "\n") attrs

--------------------------------------------------------------------------------
-- Small leaf-list helpers shared by later sections. None of these walk a
-- structure that is part of the big mutual block, so `map` is safe here.
--------------------------------------------------------------------------------

visPrefix : VisibilityQualifier -> String
visPrefix v = prefixSpace (show v)

optionalVisPrefix : Maybe (AstNode phase VisibilityQualifier) -> String
optionalVisPrefix Nothing = ""
optionalVisPrefix (Just (MkAstNode _ _ visibility)) = visPrefix visibility

showQualifiersPrefix : List (AstNode phase QuantumStorageQualifier) -> String
showQualifiersPrefix []    = ""
showQualifiersPrefix quals =
  joinWith " " (map (\(MkAstNode _ _ q) => show q) quals) ++ " "

showOnBasis : Maybe (AstNode phase String) -> String
showOnBasis Nothing                    = ""
showOnBasis (Just (MkAstNode _ _ raw)) = ".on(" ++ raw ++ ")"

showMutabilityPrefix : Maybe (AstNode phase Mutability) -> String
showMutabilityPrefix Nothing = ""
showMutabilityPrefix (Just (MkAstNode _ _ mutability)) =
  prefixSpace (show mutability)

--------------------------------------------------------------------------------
-- Patterns (Frontend.Syntax.Pattern) -- self-recursive, but independent of
-- expressions, so this is its own mutual block.
--------------------------------------------------------------------------------

mutual

  public export
  showPattern : PhasePretty phase => Pattern phase -> String
  showPattern (MkAstNode _ _ pat) = showPatternNode pat

  showPatternNode : PhasePretty phase => PatternNode phase -> String
  showPatternNode pat =
    case pat of
      PatternWildcard          => "_"
      PatternName mutability nm =>
        maybe "" (\m => prefixSpace (show m)) mutability ++ showName nm
      PatternPath p             => showPath p
      PatternLiteral lit        => showLiteral lit
      PatternParenthesized inner => parens (showPattern inner)
      PatternTuple elems         => showTupleLike (showPatternList1 elems)
      PatternArray elems         => brackets (joinWith ", " (showPatternList elems))
      PatternStruct p fields     =>
        showPath p ++ " " ++ braces (joinWith ", " (showStructPatternFieldList fields))
      PatternEnumTuple p args    =>
        showPath p ++ parens (joinWith ", " (showPatternList args))

  showPatternList : PhasePretty phase => List (Pattern phase) -> List String
  showPatternList []        = []
  showPatternList (p :: ps) = showPattern p :: showPatternList ps

  showPatternList1 : PhasePretty phase => List1 (Pattern phase) -> List String
  showPatternList1 (p ::: ps) = showPattern p :: showPatternList ps

  showStructPatternField : PhasePretty phase => StructPatternField phase -> String
  showStructPatternField (MkAstNode _ _ f) =
    case f of
      StructPatternFieldShorthand mutability nm =>
        maybe "" (\m => prefixSpace (show m)) mutability ++ showName nm
      StructPatternFieldExplicit nm pat =>
        showName nm ++ ": " ++ showPattern pat

  showStructPatternFieldList : PhasePretty phase => List (StructPatternField phase) -> List String
  showStructPatternFieldList []        = []
  showStructPatternFieldList (f :: fs) =
    showStructPatternField f :: showStructPatternFieldList fs

-- Quantum match patterns: flat, not self-recursive.
public export
showQuantumMatchPattern : PhasePretty phase => QuantumMatchPattern phase -> String
showQuantumMatchPattern (MkAstNode _ _ pat) =
  case pat of
    QuantumPatternBasisStringRaw s => s
    QuantumPatternIntegerRaw s     => s
    QuantumPatternWildcard         => "_"
    QuantumPatternQenumVariant p names =>
      showPath p ++ parens (joinWith ", " (map showName names))

--------------------------------------------------------------------------------
-- Pauli strings and stabilizer terms (Frontend.Syntax.Contract) -- these do
-- not mention expressions or names, so they too sit outside the big mutual
-- block and need no phase dictionary.
--------------------------------------------------------------------------------

showPauliString : PauliString phase -> String
showPauliString (MkAstNode _ _ (MkPauliStringNode ops)) =
  joinWith "" (map show (forget ops))

showStabilizerSign : StabilizerSign -> String
showStabilizerSign StabilizerPlus  = "+"
showStabilizerSign StabilizerMinus = "-"

showSignedPauliTerm : SignedPauliTerm phase -> String
showSignedPauliTerm (MkAstNode _ _ (MkSignedPauliTermNode sign pauli)) =
  showStabilizerSign sign ++ showPauliString pauli

--------------------------------------------------------------------------------
-- Expression precedence table
--------------------------------------------------------------------------------
-- Higher binds tighter. Only Unary/Cast/Binary/Range are "operator class":
-- these are the constructs with OPTIONAL parentheses, the ones PrettyStrict
-- forces open. Everything else either never needs parenthesizing (atoms,
-- postfix forms, ctrl/adjoint -- all self-delimited by their own syntax) or
-- always needs it when a mandatory position demands higher precedence than
-- it has (block-like control flow used as a postfix base), independent of
-- style.
--------------------------------------------------------------------------------

precAtomic, precPostfix, precUnary, precCast : Nat
precAtomic  = 110
precPostfix = 100
precUnary   = 90
precCast    = 85

precMul, precAdd, precShift, precBitAnd, precBitXor, precBitOr : Nat
precMul    = 80
precAdd    = 75
precShift  = 70
precBitAnd = 65
precBitXor = 60
precBitOr  = 55

precCompare, precLogicalAnd, precLogicalOr, precRange, precLowest : Nat
precCompare    = 50
precLogicalAnd = 45
precLogicalOr  = 40
precRange      = 30
precLowest     = 0

binaryOperatorPrecedence : BinaryOperator -> Nat
binaryOperatorPrecedence op =
  case op of
    BinaryMultiply     => precMul
    BinaryDivide       => precMul
    BinaryRemainder    => precMul
    BinaryAdd          => precAdd
    BinarySubtract     => precAdd
    BinaryShiftLeft    => precShift
    BinaryShiftRight   => precShift
    BinaryBitAnd       => precBitAnd
    BinaryBitXor       => precBitXor
    BinaryBitOr        => precBitOr
    BinaryEqual        => precCompare
    BinaryNotEqual     => precCompare
    BinaryGreater      => precCompare
    BinaryGreaterEqual => precCompare
    BinaryLess         => precCompare
    BinaryLessEqual    => precCompare
    BinaryLogicalAnd   => precLogicalAnd
    BinaryLogicalOr    => precLogicalOr

exprOwnPrecedence : ExpressionNode phase -> Nat
exprOwnPrecedence e =
  case e of
    ExprLiteral _         => precAtomic
    ExprName _             => precAtomic
    ExprPath _              => precAtomic
    ExprBuiltin _            => precAtomic
    ExprSelf _                 => precAtomic
    ExprParenthesized _        => precAtomic
    ExprTuple _                 => precAtomic
    ExprArray _                  => precAtomic
    ExprRepeatedArray _ _         => precAtomic
    ExprStructLiteral _ _          => precAtomic
    ExprCtrl _                      => precAtomic
    ExprAdjoint _                    => precAtomic
    ExprCall _ _                      => precPostfix
    ExprMethodCall _ _ _                => precPostfix
    ExprField _ _                         => precPostfix
    ExprTupleIndex _ _                      => precPostfix
    ExprIndex _ _                             => precPostfix
    ExprUnary _ _                               => precUnary
    ExprCast _ _                                  => precCast
    ExprBinary (MkAstNode _ _ op) _ _               => binaryOperatorPrecedence op
    ExprRange _ _ _                                   => precRange
    ExprBlock _                                         => precLowest
    ExprIf _                                              => precLowest
    ExprQIf _                                               => precLowest
    ExprSIf _                                                 => precLowest
    ExprMatch _                                                 => precLowest
    ExprQMatch _                                                  => precLowest
    ExprSMatch _                                                    => precLowest
    ExprLoop _                                                        => precLowest
    ExprWhile _ _                                                       => precLowest
    ExprFor _ _ _                                                         => precLowest
    ExprBreak _                                                             => precLowest
    ExprContinue                                                              => precLowest
    ExprReturn _                                                                => precLowest

isOperatorClassExpr : ExpressionNode phase -> Bool
isOperatorClassExpr e =
  case e of
    ExprUnary _ _   => True
    ExprCast _ _    => True
    ExprBinary _ _ _ => True
    ExprRange _ _ _  => True
    _                => False

--------------------------------------------------------------------------------
-- The recursive core: casts embed types, array-size positions embed
-- expressions, and expressions embed blocks whose statements contain more
-- expressions and types.
--------------------------------------------------------------------------------

-- Declaring the two cross-group entry points up front lets Idris elaborate
-- the type, expression, and block renderers separately. Their definitions
-- remain total while the internal covering boundary keeps the global cycle
-- out of a single size-change analysis.
public export
showExprAt : PhasePretty phase => PrettyStyle -> Nat -> Expr phase -> String

public export
showBlock : PhasePretty phase => PrettyStyle -> Block phase -> String

mutual

  ------------------------------------------------------------------
  -- Types (Frontend.Syntax.Type)
  ------------------------------------------------------------------

  showTyNode : PhasePretty phase => PrettyStyle -> TyNode phase (Expr phase) -> String
  showTyNode style ty =
    case ty of
      TyPrimitive p         => showTypPrimLeaf p
      TyPath p               => showPath p
      TyUnit                   => "()"
      TyParenthesized inner      => parens (showTy style inner)
      TyTuple elems                => showTupleLike (showTyList1 style elems)
      TyArray elemTy sizeE           =>
        brackets (showTy style elemTy ++ "; " ++ showExprAt style 0 sizeE)
      TySlice elemTy                   => brackets (showTy style elemTy)
      TyReference (MkAstNode _ _ borrow) innerTy =>
        showBorrowPrefixed borrow (showTy style innerTy)
      TyQualified (MkAstNode _ _ qualifier) innerTy =>
        show qualifier ++ " " ++ showTy style innerTy
      TyFunction effect params retTy =>
        (case effect of
           Nothing                     => ""
           Just (MkAstNode _ _ eff) => show eff ++ " ") ++
        "fn(" ++ joinWith ", " (showFunctionTypeParameterList style params) ++ ")" ++
        (case retTy of
           Nothing => ""
           Just t  => " -> " ++ showTy style t)

  public export
  showTy : PhasePretty phase => PrettyStyle -> Ty phase (Expr phase) -> String
  showTy style (MkAstNode _ _ ty) = showTyNode style ty

  showTyList : PhasePretty phase => PrettyStyle -> List (Ty phase (Expr phase)) -> List String
  showTyList style []        = []
  showTyList style (t :: ts) = showTy style t :: showTyList style ts

  showTyList1 : PhasePretty phase => PrettyStyle -> List1 (Ty phase (Expr phase)) -> List String
  showTyList1 style (t ::: ts) = showTy style t :: showTyList style ts

  showFunctionTypeParameterList :
       PhasePretty phase
    => PrettyStyle
    -> List (AstNode phase (FunctionTypeParameterNode phase (Expr phase)))
    -> List String
  showFunctionTypeParameterList style [] = []
  showFunctionTypeParameterList style (MkAstNode _ _ (MkFunctionTypeParameterNode nm ty) :: rest) =
    -- Not showName: a function-type parameter name is plain NameNode at
    -- every phase (never resolved), so no PhasePretty dispatch is needed.
    (prettyNameNode nm.value ++ ": " ++ showTy style ty) :: showFunctionTypeParameterList style rest

--------------------------------------------------------------------------------
-- Expressions
--------------------------------------------------------------------------------

showExprList : PhasePretty phase => PrettyStyle -> List (Expr phase) -> List String
showExprList1 : PhasePretty phase => PrettyStyle -> List1 (Expr phase) -> List String
wrapExpr : PhasePretty phase => PrettyStyle -> Nat -> ExpressionNode phase -> String
showExpressionNodeBody :
     PhasePretty phase
  => PrettyStyle
  -> ExpressionNode phase
  -> String
showFieldInitList :
     PhasePretty phase
  => PrettyStyle
  -> List (AstNode phase (FieldInitializerNode phase))
  -> List String
showClassicalIfNode : PhasePretty phase => PrettyStyle -> ClassicalIfNode phase -> String
showQuantumBranch : PhasePretty phase => PrettyStyle -> QuantumBranchNode phase -> String
showClassicalMatchArmList :
     PhasePretty phase
  => PrettyStyle
  -> List (ClassicalMatchArm phase)
  -> List String
showQuantumMatchArmList :
     PhasePretty phase
  => PrettyStyle
  -> List (QuantumMatchArm phase)
  -> List String
showControlExpr : PhasePretty phase => PrettyStyle -> ControlExpressionNode phase -> String
showAdjointExpr : PhasePretty phase => PrettyStyle -> AdjointExpressionNode phase -> String

mutual

  -- The single entry point that decides whether a child expression needs to
  -- be parenthesized, given the precedence its syntactic position requires.
  -- Exported for callers that need explicit control over the ambient
  -- precedence; `showExpr` below is the common case (no ambient requirement).
  showExprAt style outerReq (MkAstNode _ _ value) = wrapExpr style outerReq value

  public export
  showExpr : PhasePretty phase => PrettyStyle -> Expr phase -> String
  showExpr style = showExprAt style 0

--------------------------------------------------------------------------------
-- Expression precedence wrapper
--------------------------------------------------------------------------------

mutual

  wrapExpr style outerReq value =
    let body     = assert_total $ showExpressionNodeBody style value
        own      = exprOwnPrecedence value
        mustWrap = (own < outerReq) || (isPrettyStrict style && isOperatorClassExpr value)
    in if mustWrap then parens body else body

  -- Top-level (unconstrained) rendering of a raw ExpressionNode -- used by
  -- the Show instance further down.
  showExpressionNode : PhasePretty phase => PrettyStyle -> ExpressionNode phase -> String
  showExpressionNode style value = wrapExpr style 0 value

--------------------------------------------------------------------------------
-- Expression bodies
--------------------------------------------------------------------------------

mutual

  showExpressionNodeBody style value =
    case value of
      ExprLiteral lit => showLiteral lit
      ExprName nm     => showName nm
      ExprPath p      => showPath p
      ExprBuiltin b   => show b
      ExprSelf _      => "self"

      ExprParenthesized inner => parens (showExprAt style 0 inner)
      ExprTuple elems          => showTupleLike (showExprList1 style elems)
      ExprArray elems           => brackets (joinWith ", " (showExprList style elems))
      ExprRepeatedArray elemE countE =>
        brackets (showExprAt style 0 elemE ++ "; " ++ showExprAt style 0 countE)

      ExprStructLiteral p fields =>
        showPath p ++ " " ++ braces (joinWith ", " (showFieldInitList style fields))

      ExprCall callee args =>
        showExprAt style precPostfix callee ++
          "(" ++ joinWith ", " (showExprList style args) ++ ")"

      ExprMethodCall recv methodName args =>
        showExprAt style precPostfix recv ++ "." ++ showMemberName methodName ++
          "(" ++ joinWith ", " (showExprList style args) ++ ")"

      ExprField obj fld      => showExprAt style precPostfix obj ++ "." ++ showMemberName fld
      ExprTupleIndex obj idx => showExprAt style precPostfix obj ++ "." ++ idx
      ExprIndex obj idx      =>
        showExprAt style precPostfix obj ++ "[" ++ showExprAt style 0 idx ++ "]"

      ExprUnary (MkAstNode _ _ op) operand =>
        let operandStr = showExprAt style precUnary operand in
        case op of
          UnaryNegate     => "-" ++ operandStr
          UnaryLogicalNot => "!" ++ operandStr
          UnaryBorrow b   => showBorrowPrefixed b operandStr

      ExprBinary (MkAstNode _ _ op) lhs rhs =>
        let p = binaryOperatorPrecedence op in
        showExprAt style p lhs ++ " " ++ show op ++ " " ++ showExprAt style (S p) rhs

      ExprRange start (MkAstNode _ _ op) end =>
        (case start of
           Nothing => ""
           Just s  => showExprAt style (S precRange) s) ++
        show op ++
        (case end of
           Nothing => ""
           Just e  => showExprAt style (S precRange) e)

      ExprCast operand ty => showExprAt style precCast operand ++ " as " ++ showTy style ty

      ExprBlock blk => showBlock style blk

      ExprIf ifNode => showClassicalIfNode style ifNode

      ExprQIf (MkQuantumIfNode qcond thenBranch elseBranch) =>
        "qif " ++ showExprAt style 0 qcond ++ " " ++ showQuantumBranch style thenBranch ++
          (case elseBranch of
             Nothing => ""
             Just b  => " qelse " ++ showQuantumBranch style b)

      ExprSIf (MkStateIfNode scond thenE elseE) =>
        "sif " ++ showExprAt style 0 scond ++ " then " ++ showExprAt style 0 thenE ++
          " selse " ++ showExprAt style 0 elseE

      ExprMatch (MkClassicalMatchNode scrut arms) =>
        "match " ++ showExprAt style 0 scrut ++ " " ++
          braces (joinWith ", " (showClassicalMatchArmList style arms))

      ExprQMatch (MkQuantumMatchNode scrut arms) =>
        "qmatch " ++ showExprAt style 0 scrut ++ " " ++
          braces (joinWith ", " (showQuantumMatchArmList style arms))

      ExprSMatch (MkStateMatchNode scrut arms) =>
        "smatch " ++ showExprAt style 0 scrut ++ " " ++
          braces (joinWith ", " (showQuantumMatchArmList style arms))

      ExprLoop body => "loop " ++ showBlock style body

      ExprWhile cond body =>
        "while " ++ showExprAt style 0 cond ++ " " ++ showBlock style body

      ExprFor pat iterE body =>
        "for " ++ showPattern pat ++ " in " ++ showExprAt style 0 iterE ++
          " " ++ showBlock style body

      ExprBreak Nothing  => "break"
      ExprBreak (Just e) => "break " ++ showExprAt style 0 e

      ExprContinue => "continue"

      ExprReturn Nothing  => "return"
      ExprReturn (Just e) => "return " ++ showExprAt style 0 e

      ExprCtrl c    => showControlExpr style c
      ExprAdjoint a => showAdjointExpr style a

--------------------------------------------------------------------------------
-- Expression collections and struct fields
--------------------------------------------------------------------------------

mutual

  showExprList style []        = []
  showExprList style (e :: es) = showExprAt style 0 e :: showExprList style es

  showExprList1 style (e ::: es) = showExprAt style 0 e :: showExprList style es

  showFieldInit : PhasePretty phase => PrettyStyle -> AstNode phase (FieldInitializerNode phase) -> String
  showFieldInit style (MkAstNode _ _ f) =
    case f of
      FieldInitShorthand nm => showName nm
      FieldInitExplicit nm e => showName nm ++ ": " ++ showExprAt style 0 e

  showFieldInitList style []        = []
  showFieldInitList style (f :: fs) = showFieldInit style f :: showFieldInitList style fs

--------------------------------------------------------------------------------
-- if / qif / sif
--------------------------------------------------------------------------------

mutual

  showClassicalIfNode style (MkClassicalIfNode cond thenBlk elseBranch) =
    "if " ++ showExprAt style 0 cond ++ " " ++ showBlock style thenBlk ++
      (case elseBranch of
         Nothing                                          => ""
         Just (ElseBlock b)                                => " else " ++ showBlock style b
         Just (ElseChainedIf (MkAstNode _ _ chained)) =>
           " else " ++ showClassicalIfNode style chained)

  showQuantumBranch style branch =
    case branch of
      QuantumBranchBlock b      => showBlock style b
      QuantumBranchExpression e => showExprAt style 0 e

--------------------------------------------------------------------------------
-- match / qmatch / smatch
--------------------------------------------------------------------------------

mutual

  showClassicalMatchArmNode : PhasePretty phase => PrettyStyle -> ClassicalMatchArmNode phase -> String
  showClassicalMatchArmNode style (MkClassicalMatchArmNode pat guard armBody) =
    showPattern pat ++
      (case guard of
         Nothing => ""
         Just g  => " if " ++ showExprAt style 0 g) ++
      " => " ++ showExprAt style 0 armBody

  public export
  showClassicalMatchArm : PhasePretty phase => PrettyStyle -> ClassicalMatchArm phase -> String
  showClassicalMatchArm style (MkAstNode _ _ arm) = showClassicalMatchArmNode style arm

  showClassicalMatchArmList style []        = []
  showClassicalMatchArmList style (a :: as) =
    showClassicalMatchArm style a :: showClassicalMatchArmList style as

  showQuantumMatchArmNode : PhasePretty phase => PrettyStyle -> QuantumMatchArmNode phase -> String
  showQuantumMatchArmNode style (MkQuantumMatchArmNode pat armBody) =
    showQuantumMatchPattern pat ++ " => " ++ showExprAt style 0 armBody

  public export
  showQuantumMatchArm : PhasePretty phase => PrettyStyle -> QuantumMatchArm phase -> String
  showQuantumMatchArm style (MkAstNode _ _ arm) = showQuantumMatchArmNode style arm

  showQuantumMatchArmList style []        = []
  showQuantumMatchArmList style (a :: as) =
    showQuantumMatchArm style a :: showQuantumMatchArmList style as

--------------------------------------------------------------------------------
-- ctrl and adjoint
--------------------------------------------------------------------------------

mutual

  showControlExpr style c =
    case c of
      ControlledCallable controls onBasis callable =>
        "ctrl(" ++ joinWith ", " (showExprList1 style controls) ++ ")" ++
          showOnBasis onBasis ++ ".apply(" ++ showExprAt style 0 callable ++ ")"
      ControlledBlock controls onBasis body =>
        "ctrl(" ++ joinWith ", " (showExprList1 style controls) ++ ")" ++
          showOnBasis onBasis ++ " " ++ showBlock style body

  showAdjointExpr style a =
    case a of
      AdjointOfCallable callable => "adjoint(" ++ showExprAt style 0 callable ++ ")"
      AdjointBlock body          => "adjoint " ++ showBlock style body

--------------------------------------------------------------------------------
-- Blocks and statements
--------------------------------------------------------------------------------

mutual

  showBlockNode : PhasePretty phase => PrettyStyle -> BlockNode phase -> String
  showBlockNode style (MkBlockNode innerDocs stmts finalE) =
    let docsStrs  = map showDocComment innerDocs
        stmtsStrs = showStatementList style stmts
        tailStrs  = case finalE of
                      Nothing => []
                      Just e  => [showExprAt style 0 e]
        parts     = docsStrs ++ stmtsStrs ++ tailStrs
    in case parts of
         [] => "{ }"
         _  => braces (joinWith " " parts)

  showBlock style (MkAstNode _ _ blk) = showBlockNode style blk

  showStatementNode : PhasePretty phase => PrettyStyle -> StatementNode phase -> String
  showStatementNode style stmt =
    case stmt of
      StatementLet letBinding         => showLetBindingNode style letBinding ++ ";"
      StatementAssignment assignment  => showAssignmentNode style assignment ++ ";"
      StatementSemiExpression e       => showExprAt style 0 e ++ ";"
      StatementExpression e           => showExprAt style 0 e

  public export
  showStatement : PhasePretty phase => PrettyStyle -> Statement phase -> String
  showStatement style (MkAstNode _ _ stmt) = showStatementNode style stmt

  showStatementList : PhasePretty phase => PrettyStyle -> List (Statement phase) -> List String
  showStatementList style []        = []
  showStatementList style (s :: ss) = showStatement style s :: showStatementList style ss

  showLetBindingNode : PhasePretty phase => PrettyStyle -> LetBindingNode phase -> String
  showLetBindingNode style (MkLetBindingNode quals pat tyAnn maybeInit) =
    "let " ++ showQualifiersPrefix quals ++ showPattern pat ++
      (case tyAnn of
         Nothing => ""
         Just t  => ": " ++ showTy style t) ++
      (case maybeInit of
         Nothing                                       => ""
         Just (MkLetInitializerNode (MkAstNode _ _ marker) val) =>
           " " ++ show marker ++ " " ++ showExprAt style 0 val)

  public export
  showLetBinding : PhasePretty phase => PrettyStyle -> LetBinding phase -> String
  showLetBinding style (MkAstNode _ _ lb) = showLetBindingNode style lb

  showAssignmentNode : PhasePretty phase => PrettyStyle -> AssignmentNode phase -> String
  showAssignmentNode style (MkAssignmentNode (MkAstNode _ _ target) (MkAstNode _ _ op) val) =
    showAssignmentTargetNode style target ++ " " ++ show op ++ " " ++ showExprAt style 0 val

  showAssignmentTargetNode : PhasePretty phase => PrettyStyle -> AssignmentTargetNode phase -> String
  showAssignmentTargetNode style target =
    case target of
      AssignTargetName nm      => showName nm
      AssignTargetIndex obj ix =>
        showExprAt style precPostfix obj ++ "[" ++ showExprAt style 0 ix ++ "]"
      AssignTargetField obj fld => showExprAt style precPostfix obj ++ "." ++ showMemberName fld
      AssignTargetTupleIndex obj ix => showExprAt style precPostfix obj ++ "." ++ ix

  public export
  showAssignmentTarget : PhasePretty phase => PrettyStyle -> AssignmentTarget phase -> String
  showAssignmentTarget style (MkAstNode _ _ t) = showAssignmentTargetNode style t

--------------------------------------------------------------------------------
-- Contracts: requires/ensures clauses and their predicates
--------------------------------------------------------------------------------

mutual

  showContractPredicateNode : PhasePretty phase => PrettyStyle -> ContractPredicateNode phase (Expr phase) -> String
  showContractPredicateNode style predicate =
    case predicate of
      ContractClean e        => "clean(" ++ showExprAt style 0 e ++ ")"
      ContractBasis e pauli  =>
        "basis(" ++ showExprAt style 0 e ++ ", " ++ showPauliString pauli ++ ")"
      ContractSeparable e    => "separable(" ++ showExprAt style 0 e ++ ")"
      ContractIsolated e     => "isolated(" ++ showExprAt style 0 e ++ ")"
      ContractProduct e (x ::: xs) =>
        "product(" ++
          joinWith ", " (showExprAt style 0 e :: showExprAt style 0 x :: showExprList style xs) ++
          ")"
      ContractStabilized e terms =>
        "stabilized(" ++ showExprAt style 0 e ++ ", [" ++
          joinWith ", " (map showSignedPauliTerm (forget terms)) ++ "])"

  public export
  showContractPredicate : PhasePretty phase => PrettyStyle -> ContractPredicate phase (Expr phase) -> String
  showContractPredicate style (MkAstNode _ _ p) = showContractPredicateNode style p

  showContractClauseNode : PhasePretty phase => PrettyStyle -> ContractClauseNode phase (Expr phase) -> String
  showContractClauseNode style clause =
    case clause of
      RequiresClause p => "requires " ++ showContractPredicate style p
      EnsuresClause p  => "ensures " ++ showContractPredicate style p

  public export
  showContractClause : PhasePretty phase => PrettyStyle -> ContractClause phase (Expr phase) -> String
  showContractClause style (MkAstNode _ _ c) = showContractClauseNode style c

  showContractClauseList : PhasePretty phase => PrettyStyle -> List (ContractClause phase (Expr phase)) -> List String
  showContractClauseList style []        = []
  showContractClauseList style (c :: cs) =
    showContractClause style c :: showContractClauseList style cs

--------------------------------------------------------------------------------
-- Function declarations and parameters
--------------------------------------------------------------------------------

mutual

  showFunctionParameterNode : PhasePretty phase => PrettyStyle -> FunctionParameterNode phase -> String
  showFunctionParameterNode style p =
    case p of
      NormalParameter docs mutability nm ty =>
        docsPrefix docs ++ showMutabilityPrefix mutability ++
        showName nm ++ ": " ++ showTy style ty
      ReceiverParameter docs Nothing => docsPrefix docs ++ "self"
      ReceiverParameter docs (Just (MkAstNode _ _ borrow)) =>
        docsPrefix docs ++
          (case borrow of
             SharedBorrow  => "&self"
             MutableBorrow => "&mut self")

  public export
  showFunctionParameter : PhasePretty phase => PrettyStyle -> FunctionParameter phase -> String
  showFunctionParameter style (MkAstNode _ _ p) = showFunctionParameterNode style p

  showFunctionParameterList : PhasePretty phase => PrettyStyle -> List (FunctionParameter phase) -> List String
  showFunctionParameterList style []        = []
  showFunctionParameterList style (p :: ps) =
    showFunctionParameter style p :: showFunctionParameterList style ps

  showFunctionDeclarationNode : PhasePretty phase => PrettyStyle -> FunctionDeclarationNode phase -> String
  showFunctionDeclarationNode style
    (MkFunctionDeclarationNode docs attrs vis constness effect nm params retTy supports contracts body) =
    let visibilityStr = case vis of
                          Nothing                       => ""
                          Just (MkAstNode _ _ visibility) => visPrefix visibility
        effectStr = case effect of
                      Nothing                        => ""
                      Just (MkAstNode _ _ eff)  => show eff ++ " "
        constStr    = case constness of
                        Nothing                         => ""
                        Just (MkAstNode _ _ qualifier) => show qualifier ++ " "
        paramsStr   = joinWith ", " (showFunctionParameterList style params)
        retStr      = case retTy of
                        Nothing => ""
                        Just t  => " -> " ++ showTy style t
        supportsStr = case supports of
                        [] => ""
                        _  => " supports " ++
                              joinWith ", " (map (\(MkAstNode _ _ k) => show k) supports)
        contractsStr = concatMap (\c => " " ++ c) (showContractClauseList style contracts)
    in docsPrefix docs ++ attrsPrefix attrs ++ visibilityStr ++ constStr ++ effectStr ++
       "fn " ++ showName nm ++ "(" ++ paramsStr ++ ")" ++ retStr ++ supportsStr ++
       contractsStr ++ " " ++ showBlock style body

  public export
  showFunctionDeclaration : PhasePretty phase => PrettyStyle -> FunctionDeclaration phase -> String
  showFunctionDeclaration style (MkAstNode _ _ fd) = showFunctionDeclarationNode style fd

  showImplFunctionList :
       PhasePretty phase => PrettyStyle -> List (FunctionDeclaration phase) -> List String
  showImplFunctionList style []        = []
  showImplFunctionList style (MkAstNode _ _ fd :: rest) =
    showFunctionDeclarationNode style fd :: showImplFunctionList style rest

--------------------------------------------------------------------------------
-- struct / enum / qenum declarations
--------------------------------------------------------------------------------

mutual

  showStructField : PhasePretty phase => PrettyStyle -> AstNode phase (StructFieldNode phase) -> String
  showStructField style (MkAstNode _ _ (MkStructFieldNode docs nm ty)) =
    docsPrefix docs ++ showName nm ++ ": " ++ showTy style ty

  showStructFieldList :
       PhasePretty phase => PrettyStyle -> List (AstNode phase (StructFieldNode phase)) -> List String
  showStructFieldList style []        = []
  showStructFieldList style (f :: fs) = showStructField style f :: showStructFieldList style fs

  showStructDeclarationNode : PhasePretty phase => PrettyStyle -> StructDeclarationNode phase -> String
  showStructDeclarationNode style (MkStructDeclarationNode docs attrs vis nm fields) =
    docsPrefix docs ++ attrsPrefix attrs ++ optionalVisPrefix vis ++ "struct " ++ showName nm ++
      " " ++ braces (joinWith ", " (showStructFieldList style fields))

  public export
  showStructDeclaration : PhasePretty phase => PrettyStyle -> StructDeclaration phase -> String
  showStructDeclaration style (MkAstNode _ _ sd) = showStructDeclarationNode style sd

  showEnumVariantBody : PhasePretty phase => PrettyStyle -> EnumVariantBody phase -> String
  showEnumVariantBody style body =
    case body of
      VariantUnit          => ""
      VariantTuple tys      => parens (joinWith ", " (showTyList1 style tys))
      VariantStruct fields   => " " ++ braces (joinWith ", " (showStructFieldList style fields))

  showEnumVariant : PhasePretty phase => PrettyStyle -> AstNode phase (EnumVariantNode phase) -> String
  showEnumVariant style (MkAstNode _ _ (MkEnumVariantNode docs nm body)) =
    docsPrefix docs ++ showName nm ++ showEnumVariantBody style body

  showEnumVariantList :
       PhasePretty phase => PrettyStyle -> List (AstNode phase (EnumVariantNode phase)) -> List String
  showEnumVariantList style []        = []
  showEnumVariantList style (v :: vs) = showEnumVariant style v :: showEnumVariantList style vs

  showEnumDeclarationNode : PhasePretty phase => PrettyStyle -> EnumDeclarationNode phase -> String
  showEnumDeclarationNode style (MkEnumDeclarationNode docs attrs vis nm variants) =
    docsPrefix docs ++ attrsPrefix attrs ++ optionalVisPrefix vis ++ "enum " ++ showName nm ++
      " " ++ braces (joinWith ", " (showEnumVariantList style variants))

  public export
  showEnumDeclaration : PhasePretty phase => PrettyStyle -> EnumDeclaration phase -> String
  showEnumDeclaration style (MkAstNode _ _ ed) = showEnumDeclarationNode style ed

  showQEnumVariant : PhasePretty phase => PrettyStyle -> AstNode phase (QEnumVariantNode phase) -> String
  showQEnumVariant style (MkAstNode _ _ (MkQEnumVariantNode docs nm payloadTys)) =
    docsPrefix docs ++ showName nm ++ parens (joinWith ", " (showTyList1 style payloadTys))

  showQEnumVariantList :
       PhasePretty phase => PrettyStyle -> List (AstNode phase (QEnumVariantNode phase)) -> List String
  showQEnumVariantList style []        = []
  showQEnumVariantList style (v :: vs) = showQEnumVariant style v :: showQEnumVariantList style vs

  showQEnumDeclarationNode : PhasePretty phase => PrettyStyle -> QEnumDeclarationNode phase -> String
  showQEnumDeclarationNode style (MkQEnumDeclarationNode docs attrs vis nm variants) =
    docsPrefix docs ++ attrsPrefix attrs ++ optionalVisPrefix vis ++ "qenum " ++ showName nm ++
      " " ++ braces (joinWith ", " (showQEnumVariantList style variants))

  public export
  showQEnumDeclaration : PhasePretty phase => PrettyStyle -> QEnumDeclaration phase -> String
  showQEnumDeclaration style (MkAstNode _ _ qd) = showQEnumDeclarationNode style qd

--------------------------------------------------------------------------------
-- impl / const / use declarations
--------------------------------------------------------------------------------

mutual

  showImplDeclarationNode : PhasePretty phase => PrettyStyle -> ImplDeclarationNode phase -> String
  showImplDeclarationNode style (MkImplDeclarationNode docs target fns) =
    docsPrefix docs ++ "impl " ++ showPath target ++ " " ++
      braces (joinWith " " (showImplFunctionList style fns))

  public export
  showImplDeclaration : PhasePretty phase => PrettyStyle -> ImplDeclaration phase -> String
  showImplDeclaration style (MkAstNode _ _ impl) = showImplDeclarationNode style impl

  showConstDeclarationNode : PhasePretty phase => PrettyStyle -> ConstDeclarationNode phase -> String
  showConstDeclarationNode style (MkConstDeclarationNode docs vis nm ty val) =
    docsPrefix docs ++ optionalVisPrefix vis ++ "const " ++ showName nm ++ ": " ++ showTy style ty ++
      " = " ++ showExprAt style 0 val ++ ";"

  public export
  showConstDeclaration : PhasePretty phase => PrettyStyle -> ConstDeclaration phase -> String
  showConstDeclaration style (MkAstNode _ _ cd) = showConstDeclarationNode style cd

  showUseDeclarationNode : PhasePretty phase => PrettyStyle -> UseDeclarationNode phase -> String
  showUseDeclarationNode style (MkUseDeclarationNode docs vis path alias) =
    docsPrefix docs ++ optionalVisPrefix vis ++ "use " ++ showPath path ++
      maybe "" (\name => " as " ++ showPlainName name) alias ++ ";"

  public export
  showUseDeclaration : PhasePretty phase => PrettyStyle -> UseDeclaration phase -> String
  showUseDeclaration style (MkAstNode _ _ ud) = showUseDeclarationNode style ud

--------------------------------------------------------------------------------
-- Modules and items are mutually recursive through inline module bodies.
--------------------------------------------------------------------------------

mutual

  showModuleDeclarationNode : PhasePretty phase => PrettyStyle -> ModuleDeclarationNode phase -> String
  showModuleDeclarationNode style (MkModuleDeclarationNode docs vis nm body) =
    docsPrefix docs ++ optionalVisPrefix vis ++ "mod " ++ showName nm ++ showModuleBody style body

  showModuleBody : PhasePretty phase => PrettyStyle -> ModuleBody phase -> String
  showModuleBody style body =
    case body of
      ModuleInline innerDocs items =>
        " " ++ braces (joinWith "\n" (map showDocComment innerDocs ++ showItemList style items))
      ModuleExternal => ";"

  public export
  showModuleDeclaration : PhasePretty phase => PrettyStyle -> ModuleDeclaration phase -> String
  showModuleDeclaration style (MkAstNode _ _ md) = showModuleDeclarationNode style md

  ------------------------------------------------------------------
  -- Items
  ------------------------------------------------------------------

  showItemNode : PhasePretty phase => PrettyStyle -> ItemNode phase -> String
  showItemNode style item =
    case item of
      ItemFunction fd => showFunctionDeclarationNode style fd
      ItemStruct sd   => showStructDeclarationNode style sd
      ItemEnum ed     => showEnumDeclarationNode style ed
      ItemQEnum qd    => showQEnumDeclarationNode style qd
      ItemImpl impl   => showImplDeclarationNode style impl
      ItemConst cd    => showConstDeclarationNode style cd
      ItemUse ud      => showUseDeclarationNode style ud
      ItemModule md   => showModuleDeclarationNode style md

  public export
  showItem : PhasePretty phase => PrettyStyle -> Item phase -> String
  showItem style (MkAstNode _ _ item) = showItemNode style item

  showItemList : PhasePretty phase => PrettyStyle -> List (Item phase) -> List String
  showItemList style []        = []
  showItemList style (i :: is) = showItem style i :: showItemList style is

--------------------------------------------------------------------------------
-- Source files
--------------------------------------------------------------------------------

mutual

  showSourceFileNode : PhasePretty phase => PrettyStyle -> SourceFileNode phase -> String
  showSourceFileNode style (MkSourceFileNode innerDocs items) =
    joinWith "\n" (map showDocComment innerDocs ++ showItemList style items)

  public export
  showSourceFile : PhasePretty phase => PrettyStyle -> SourceFile phase -> String
  showSourceFile style (MkAstNode _ _ sf) = showSourceFileNode style sf

--------------------------------------------------------------------------------
-- Public convenience wrappers
--------------------------------------------------------------------------------

public export
showSourceFileLax : PhasePretty phase => SourceFile phase -> String
showSourceFileLax = showSourceFile PrettyLax

public export
showSourceFileStrict : PhasePretty phase => SourceFile phase -> String
showSourceFileStrict = showSourceFile PrettyStrict

public export
showExprLax : PhasePretty phase => Expr phase -> String
showExprLax = showExprAt PrettyLax 0

public export
showExprStrict : PhasePretty phase => Expr phase -> String
showExprStrict = showExprAt PrettyStrict 0

public export
showBlockLax : PhasePretty phase => Block phase -> String
showBlockLax = showBlock PrettyLax

public export
showBlockStrict : PhasePretty phase => Block phase -> String
showBlockStrict = showBlock PrettyStrict

public export
showItemLax : PhasePretty phase => Item phase -> String
showItemLax = showItem PrettyLax

public export
showItemStrict : PhasePretty phase => Item phase -> String
showItemStrict = showItem PrettyStrict

public export
showTyLax : PhasePretty phase => Ty phase (Expr phase) -> String
showTyLax = showTy PrettyLax

public export
showTyStrict : PhasePretty phase => Ty phase (Expr phase) -> String
showTyStrict = showTy PrettyStrict

--------------------------------------------------------------------------------
-- Show instances on the raw (un-located) payload types. Frontend.ASTPhases
-- implements `Show a => Show (AstNode phase a)` generically by printing
-- `value` alone and skipping AstInfo/metadata -- so giving each raw type
-- below a Show instance is enough for every located alias in
-- Frontend.Syntax.AST to be `Show` automatically, always in PrettyLax style
-- and for any phase with a `PhasePretty` instance. Call showXxxStrict (or the
-- showXxx style-taking functions above) directly when strict style is wanted.
--------------------------------------------------------------------------------

public export
PhasePretty phase => Show (ExpressionNode phase) where
  show = showExpressionNode PrettyLax

public export
PhasePretty phase => Show (BlockNode phase) where
  show = showBlockNode PrettyLax

public export
PhasePretty phase => Show (StatementNode phase) where
  show = showStatementNode PrettyLax

public export
PhasePretty phase => Show (ItemNode phase) where
  show = showItemNode PrettyLax

public export
PhasePretty phase => Show (TyNode phase (Expr phase)) where
  show = showTyNode PrettyLax

public export
PhasePretty phase => Show (ContractClauseNode phase (Expr phase)) where
  show = showContractClauseNode PrettyLax

public export
PhasePretty phase => Show (ContractPredicateNode phase (Expr phase)) where
  show = showContractPredicateNode PrettyLax

public export
PhasePretty phase => Show (SourceFileNode phase) where
  show = showSourceFileNode PrettyLax

public export
PhasePretty phase => Show (FunctionDeclarationNode phase) where
  show = showFunctionDeclarationNode PrettyLax

public export
PhasePretty phase => Show (FunctionParameterNode phase) where
  show = showFunctionParameterNode PrettyLax

public export
PhasePretty phase => Show (StructDeclarationNode phase) where
  show = showStructDeclarationNode PrettyLax

public export
PhasePretty phase => Show (EnumDeclarationNode phase) where
  show = showEnumDeclarationNode PrettyLax

public export
PhasePretty phase => Show (QEnumDeclarationNode phase) where
  show = showQEnumDeclarationNode PrettyLax

public export
PhasePretty phase => Show (ImplDeclarationNode phase) where
  show = showImplDeclarationNode PrettyLax

public export
PhasePretty phase => Show (ConstDeclarationNode phase) where
  show = showConstDeclarationNode PrettyLax

public export
PhasePretty phase => Show (UseDeclarationNode phase) where
  show = showUseDeclarationNode PrettyLax

public export
PhasePretty phase => Show (ModuleDeclarationNode phase) where
  show = showModuleDeclarationNode PrettyLax

public export
PhasePretty phase => Show (LetBindingNode phase) where
  show = showLetBindingNode PrettyLax

public export
PhasePretty phase => Show (AssignmentTargetNode phase) where
  show = showAssignmentTargetNode PrettyLax

public export
PhasePretty phase => Show (ClassicalMatchArmNode phase) where
  show = showClassicalMatchArmNode PrettyLax

public export
PhasePretty phase => Show (QuantumMatchArmNode phase) where
  show = showQuantumMatchArmNode PrettyLax
