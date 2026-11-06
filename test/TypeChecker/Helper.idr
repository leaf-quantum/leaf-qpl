module TypeChecker.Helper

import Data.List1
import Data.String
import Text.Bounds

import Compiler.Desugar.Desugar
import Compiler.ScopeAndNameResolution.Data
import Compiler.ScopeAndNameResolution.Resolve
import Compiler.ScopeAndNameResolution.Validate
import Compiler.TypeChecker.Data
import Compiler.TypeChecker.Type
import Compiler.TypeChecker.TypeCheck
import Compiler.Validation.PostParseValidation
import Frontend.ASTPhases
import Frontend.Lexer.Error
import Frontend.Lexer.Lexer
import Frontend.Parser.Error
import Frontend.Parser.Parser
import Frontend.Source
import Frontend.Syntax.AST
import Frontend.Syntax.Common
import Frontend.Syntax.Operator
import Frontend.Token
import Frontend.Utils.ASTPrettyPrinter

%default total

export
lexParseDesugarResolveAndTypeCheck : String -> String -> Either TypeError TypedSourceFile
lexParseDesugarResolveAndTypeCheck fileName inputProgram =
  case lexFile inputProgram of
    Left err => invalidFixture (renderLexerError err)
    Right tokens => case parseFile fileName tokens of
      Left err => invalidFixture (showParseError err)
      Right surfaceSourceFile => case validateSourceFile surfaceSourceFile of
        errors@(_ :: _) =>
          invalidFixture ("Validation errors:\n" ++ joinBy "\n" (map interpolate errors))
        [] =>
          let canonicalSourceFile = desugarSurfaceSyntax surfaceSourceFile
          in case resolveCanonicalSyntax canonicalSourceFile of
            Left err => invalidFixture (show err)
            Right resolvedModule => case validateResolvedModule resolvedModule of
              errors@(_ :: _) =>
                invalidFixture ("Resolution invariant errors:\n" ++ joinBy "\n" (map show errors))
              [] => case typeCheck resolvedModule of
                Left err => Left err
                Right typedModule => Right typedModule.ast
  where
    invalidFixture : String -> Either TypeError TypedSourceFile
    invalidFixture message =
      assert_total $ idris_crash $ "Invalid type-checking fixture (" ++ fileName ++ "):\n" ++ message

export
typeCheckAndPrettyPrint : String -> Either TypeError String
typeCheckAndPrettyPrint inputProgram =
  map showSourceFileStrict (lexParseDesugarResolveAndTypeCheck "test-fixture.rs" inputProgram)

--------------------------------------------------------------------------------
-- Expected outcomes
--------------------------------------------------------------------------------
-- A test compares `typeCheckOutcome program` with `accepted` or with
-- `rejectedWith err`. Errors are compared through `show`, which renders a
-- span by its start only, so `spanAt line column` is all an expected error
-- needs to say where it is. Where the plan rejects a form without naming its
-- diagnostic, `rejected (typeCheckOutcome program)` is compared with `True`.
--------------------------------------------------------------------------------

||| `Right ()` when the program type-checks, otherwise the error it reports, shown.
export
typeCheckOutcome : String -> Either String ()
typeCheckOutcome inputProgram = bimap show (const ()) (typeCheckAndPrettyPrint inputProgram)

||| The pretty-printed typed AST, or the error reported instead, shown.
export
printedTypedAst : String -> Either String String
printedTypedAst inputProgram = mapFst show (typeCheckAndPrettyPrint inputProgram)

export
accepted : Either String ()
accepted = Right ()

export
rejectedWith : TypeError -> Either String ()
rejectedWith err = Left (show err)

||| `True` when the program is rejected with any error. A fixture that fails
||| the frontend still crashes the helper rather than counting as rejected.
export
rejected : Either String () -> Bool
rejected (Left _) = True
rejected (Right ()) = False

||| A span of the test fixture starting at `line` and `column`, both 1-based.
export
spanAt : Nat -> Nat -> SourceSpan
spanAt line column =
  MkSourceSpan "test-fixture.rs" (MkSourcePos line column) (MkSourcePos line column)

--------------------------------------------------------------------------------
-- Types in expected errors
--------------------------------------------------------------------------------

export
i8 : LeafType
i8 = LeafPrimitiveType TypPrimI8

export
i16 : LeafType
i16 = LeafPrimitiveType TypPrimI16

export
i32 : LeafType
i32 = LeafPrimitiveType TypPrimI32

export
i64 : LeafType
i64 = LeafPrimitiveType TypPrimI64

export
u8 : LeafType
u8 = LeafPrimitiveType TypPrimU8

export
u32 : LeafType
u32 = LeafPrimitiveType TypPrimU32

export
u64 : LeafType
u64 = LeafPrimitiveType TypPrimU64

export
f32 : LeafType
f32 = LeafPrimitiveType TypPrimF32

export
f64 : LeafType
f64 = LeafPrimitiveType TypPrimF64

export
bool : LeafType
bool = LeafPrimitiveType TypPrimBool

export
bit : LeafType
bit = LeafPrimitiveType TypPrimBit

export
angle64 : LeafType
angle64 = LeafPrimitiveType TypPrimAngle64

export
param : LeafType
param = LeafPrimitiveType TypPrimParam

export
unit : LeafType
unit = LeafUnitType

export
linearQbit : LeafType
linearQbit = LeafQualifiedType QuantumMultiplicityLinear (LeafPrimitiveType TypPrimQbit)

export
affineQbit : LeafType
affineQbit = LeafQualifiedType QuantumMultiplicityAffine (LeafPrimitiveType TypPrimQbit)

||| `&qbit`: a reference to a linear or an affine qbit.
export
qbitRef : LeafType
qbitRef = LeafReferenceType SharedBorrow (LeafPrimitiveType TypPrimQbit)

export
array : LeafType -> Nat -> LeafType
array = LeafArrayType

export
slice : LeafType -> LeafType
slice = LeafSliceType

export
ref : LeafType -> LeafType
ref = LeafReferenceType SharedBorrow

export
refMut : LeafType -> LeafType
refMut = LeafReferenceType MutableBorrow

||| The tuple of the given element types; the empty tuple is unit.
export
tuple : List LeafType -> LeafType
tuple [] = LeafUnitType
tuple (first :: rest) = LeafTupleType (first ::: rest)

||| A function type without declared capabilities, as every written function type is.
export
fnType : FunctionEffect -> List LeafType -> LeafType -> LeafType
fnType effect parameterTypes resultType = LeafFunctionType effect [] parameterTypes resultType
