module Compiler.TypeChecker.Helper

import Compiler.Type
import Data.List
import Data.List1
import Data.Maybe
import Frontend.ASTData
import Frontend.ASTPhases
import Frontend.QuantumAnnotations
import Frontend.Syntax.AST
import Frontend.Syntax.Common
import Frontend.Syntax.Literal
import Frontend.Syntax.Name
import Frontend.Syntax.Operator
import Frontend.Syntax.Type

%default total

||| Crash on a language feature that typechecking does not support yet.
export
notImplemented : (function : String) -> (feature : String) -> a
notImplemented function feature =
  assert_total $ idris_crash $
    "Scope and name resolution, " ++ function ++ ": not yet implemented: " ++ feature ++ "."

||| Crash on a violated internal invariant: a compiler bug, not invalid Leaf source.
export
unreachable : (function : String) -> (reason : String) -> a
unreachable function reason =
  assert_total $ idris_crash $
    "Scope and name resolution, " ++ function ++ ": internal error: " ++ reason ++ "."

-- Value of an integer literal's raw spelling: digit separators, a 0x/0o/0b
-- prefix and an integer type suffix are accepted, e.g. "1_000", "0xff_u8".
integerLiteralValue : String -> Maybe Nat
integerLiteralValue raw =
  let (base, rest) = splitBase (filter (/= '_') (unpack raw))
      (digits, suffix) = span (isDigitInBase base) rest
  in if null digits || not (validSuffix suffix)
       then Nothing
       else Just $ foldl (\value, digit => value * base + fromMaybe 0 (digitValue digit)) 0 digits
  where
    splitBase : List Char -> (Nat, List Char)
    splitBase ('0' :: 'x' :: digits) = (16, digits)
    splitBase ('0' :: 'o' :: digits) = (8, digits)
    splitBase ('0' :: 'b' :: digits) = (2, digits)
    splitBase digits = (10, digits)

    digitValue : Char -> Maybe Nat
    digitValue c =
      if isDigit c
        then Just (cast (ord c - ord '0'))
        else let lower = toLower c in
          if lower >= 'a' && lower <= 'f' then Just (cast (ord lower - ord 'a' + 10)) else Nothing

    isDigitInBase : Nat -> Char -> Bool
    isDigitInBase base c = maybe False (< base) (digitValue c)

    validSuffix : List Char -> Bool
    validSuffix [] = True
    validSuffix suffix =
      pack suffix `elem` ["i8", "i16", "i32", "i64", "i128", "u8", "u16", "u32", "u64", "u128"]

-- Usage defaults to linear when only `scratch` is written.
toStorageProperties : List1 QuantumStorageQualifier -> QuantumStorageProperties
toStorageProperties qualifiers =
  let written = forget qualifiers
      usages = mapMaybe usageOf written
      scratchCount = length (filter (== QualifierScratch) written)
  in case (usages, scratchCount <= 1) of
       ([], True) => MkQuantumStorageProperties Linear (scratchCount == 1)
       ([usage], True) => MkQuantumStorageProperties usage (scratchCount == 1)
       _ => notImplemented {function = "toStorageProperties"} {feature = "diagnostics for conflicting or repeated qualifiers"}
  where
    usageOf : QuantumStorageQualifier -> Maybe QubitTypeQualifier
    usageOf QualifierLinear = Just Linear
    usageOf QualifierAffine = Just Affine
    usageOf QualifierScratch = Nothing

-- Only resolved paths carry the SymbolId of the type they name.
pathTarget : {astPhase : AstPhase} -> Path astPhase -> SymbolId
pathTarget {astPhase = SurfaceAstPhase} _ =
  unreachable {function = "pathTarget"} {reason = "type paths are resolved before typechecking"}
pathTarget {astPhase = CanonicalAstPhase} _ =
  unreachable {function = "pathTarget"} {reason = "type paths are resolved before typechecking"}
pathTarget {astPhase = ResolvedAstPhase} path = path.value.resolvedPathTargetSymbolId
pathTarget {astPhase = TypedAstPhase} path = path.value.resolvedPathTargetSymbolId

||| Translate a written type into the semantic type it denotes.
export
toLeafType : {astPhase : AstPhase} -> Ty astPhase (Expr astPhase) -> LeafType
toLeafType typeAstNode@(MkAstNode _ _ typeNode) =
  case typeNode of
    TyPrimitive primitiveName =>
      LeafPrimitive primitiveName
    TyPath typePath =>
      LeafNamed (pathTarget typePath)
    TyUnit =>
      LeafUnit
    TyParenthesized innerType =>
      recur innerType
    TyTuple elementTypes =>
      LeafTuple (map recur elementTypes)
    TyArray elementType sizeExpression =>
      LeafArray (recur elementType) (arrayLength sizeExpression)
    TySlice elementType =>
      LeafSlice (recur elementType)
    TyReference borrowKind referencedType =>
      LeafReference borrowKind.value (recur referencedType)
    TyQualified storageQualifiers qualifiedType =>
      LeafQualified (toStorageProperties (map (.value) storageQualifiers)) (recur qualifiedType)
    TyFunction functionEffect functionParameters returnType =>
      LeafFunction
        (maybe EffectGeneral (.value) functionEffect)
        (map (\parameter => recur parameter.value.parameterType) functionParameters)
        (maybe LeafUnit recur returnType)
  where
    recur : Ty astPhase (Expr astPhase) -> LeafType
    recur nestedType = toLeafType (assert_smaller typeAstNode nestedType)

    -- Named constants and constant expressions need const evaluation, which
    -- requires typechecker state.
    arrayLength : Expr astPhase -> Nat
    arrayLength (MkAstNode _ _ (ExprLiteral (MkAstNode _ _ (LiteralIntegerRaw raw)))) =
      case integerLiteralValue raw of
        Just length => length
        Nothing => unreachable {function = "toLeafType"} {reason = "the lexer accepted a malformed integer literal: " ++ raw}
    arrayLength _ =
      notImplemented {function = "toLeafType"} {feature = "array lengths other than integer literals"}

