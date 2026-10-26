module Compiler.TypeChecker.Helper

import Compiler.Type
import Compiler.TypeChecker.Data
import Data.List
import Data.List1
import Data.Maybe
import Frontend.ASTData
import Frontend.ASTPhases
import Frontend.Syntax.AST
import Frontend.Syntax.Common
import Frontend.Syntax.Literal
import Frontend.Syntax.Name
import Frontend.Syntax.Operator
import Frontend.Syntax.Type
import Frontend.Token

%default total

||| Crash on a language feature that typechecking does not support yet.
export
notImplemented : (function : String) -> (feature : String) -> a
notImplemented function feature =
  assert_total $ idris_crash $
    "Typechecking, " ++ function ++ ": not yet implemented: " ++ feature ++ "."

||| Crash on a violated internal invariant: a compiler bug, not invalid Leaf source.
export
unreachable : (function : String) -> (reason : String) -> a
unreachable function reason =
  assert_total $ idris_crash $
    "Typechecking, " ++ function ++ ": internal error: " ++ reason ++ "."

-- Only resolved paths carry the SymbolId of the type they name.
pathTarget : {astPhase : AstPhase} -> Path astPhase -> SymbolId
pathTarget {astPhase = SurfaceAstPhase} _ =
  unreachable {function = "pathTarget"} {reason = "type paths are resolved before typechecking"}
pathTarget {astPhase = CanonicalAstPhase} _ =
  unreachable {function = "pathTarget"} {reason = "type paths are resolved before typechecking"}
pathTarget {astPhase = ResolvedAstPhase} path = path.value.resolvedPathTargetSymbolId
pathTarget {astPhase = TypedAstPhase} path = path.value.resolvedPathTargetSymbolId

-- Nothing when the type contains an array length that needs const evaluation.
writtenLeafType : {astPhase : AstPhase} -> Ty astPhase (Expr astPhase) -> Maybe LeafType
writtenLeafType typeAstNode@(MkAstNode _ _ typeNode) =
  case typeNode of
    TyPrimitive primitiveName =>
      Just (LeafPrimitiveType primitiveName)
    TyPath typePath =>
      Just (LeafNamedType (pathTarget typePath))
    TyUnit =>
      Just LeafUnitType
    TyParenthesized innerType =>
      recur innerType
    TyTuple elementTypes =>
      LeafTupleType <$> traverse recur elementTypes
    TyArray elementType sizeExpression =>
      LeafArrayType <$> recur elementType <*> arrayLength sizeExpression
    TySlice elementType =>
      LeafSliceType <$> recur elementType
    TyReference borrowKind referencedType =>
      quantumMultiplicityFreeReference borrowKind.value <$> recur referencedType
    TyQualified multiplicityQualifier qualifiedType =>
      LeafQualifiedType multiplicityQualifier.value <$> recur qualifiedType
    TyFunction functionEffect functionParameters returnType =>
      LeafFunctionType (maybe EffectGeneral (.value) functionEffect)
        <$> traverse (\parameter => recur parameter.value.parameterType) functionParameters
        <*> maybe (Just LeafUnitType) recur returnType
  where
    recur : Ty astPhase (Expr astPhase) -> Maybe LeafType
    recur nestedType = writtenLeafType (assert_smaller typeAstNode nestedType)

    -- Named constants and constant expressions need const evaluation, which
    -- requires typechecker state.
    arrayLength : Expr astPhase -> Maybe Nat
    arrayLength (MkAstNode _ _ (ExprLiteral (MkAstNode _ _ (LiteralIntegerRaw raw)))) =
      case (integerLiteralValue raw, arrayLengthProblem raw) of
        (Just length, Nothing) => Just length
        (Just _, Just _) => unreachable {function = "writtenLeafType"} {reason = "post-parse validation rejects this array length: " ++ raw}
        (Nothing, _) => unreachable {function = "writtenLeafType"} {reason = "the lexer accepted a malformed integer literal: " ++ raw}
    arrayLength _ = Nothing

||| Translate a written type into the semantic type it denotes, or
||| TypeNotYetResolved when an array length needs const evaluation.
export
toInferredType : {astPhase : AstPhase} -> Ty astPhase (Expr astPhase) -> InferredType
toInferredType writtenType = maybe TypeNotYetResolved ResolvedType (writtenLeafType writtenType)

