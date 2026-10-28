module Parser.Helper

import Data.String
import Text.Bounds
import Test.Simple

import Frontend.Lexer.Error
import Frontend.Lexer.Lexer
import Frontend.ASTPhases
import Frontend.Parser.Error
import Frontend.Parser.Parser
import Frontend.Source
import Frontend.Syntax.AST
import Frontend.Utils.ASTDebugPrinter
import Frontend.Utils.ASTPrettyPrinter
import Frontend.Token

%default total

export
lexThenParse : String -> String -> Maybe SurfaceSourceFile
lexThenParse fileName inputProgram =
  case lexFile inputProgram of
      Left _ => Nothing
      Right tokens => case parseFile fileName tokens of
        Left _ => Nothing
        Right ast => Just ast

export
parseAndPrettyPrint : String -> Maybe String
parseAndPrettyPrint inputProgram =
  case lexThenParse "test-fixture.rs" inputProgram of
    Nothing => Nothing
    Just sourceFile => Just (showSourceFileStrict sourceFile)

||| Starts collecting digits when a node identifier marker is seen.
startNodeIdMarker : Char -> Maybe (SnocList Char)
startNodeIdMarker '#' = Just [<]
startNodeIdMarker _ = Nothing

||| Emits one collected identifier, if any, ahead of the remaining identifiers.
emitNodeId : SnocList Char -> List Nat -> List Nat
emitNodeId [<] remaining = remaining
emitNodeId digits remaining =
  stringToNatOrZ (pack (digits <>> [])) :: remaining

||| Scans a debug rendering for the `#<digits>` node identifiers it prints.
||| `collecting` holds the digits seen since the last `#`, which keeps the scan
||| structurally recursive on the remaining characters. A `#` that is not
||| followed by digits, such as an attribute's `#[`, collects nothing.
scanNodeIds :
     (remaining : List Char)
  -> (collecting : Maybe (SnocList Char))
  -> List Nat
scanNodeIds [] Nothing = []
scanNodeIds [] (Just digits) = emitNodeId digits []
scanNodeIds (character :: rest) (Just digits) =
  if isDigit character
    then scanNodeIds rest (Just (digits :< character))
    else emitNodeId digits (scanNodeIds rest (startNodeIdMarker character))
scanNodeIds (character :: rest) Nothing =
  scanNodeIds rest (startNodeIdMarker character)

||| The AST node identifiers in the order the debug traversal emits them, which
||| is source-tree pre-order. Identifier allocation is part of the parser's
||| contract but is invisible to the pretty printer, so tests that need to pin
||| it use this instead of `parseAndPrettyPrint`.
||| Covering rather than total because the debug traversal it reads is itself
||| declared `%default covering`.
export
covering
debugAstOf : String -> Maybe String
debugAstOf inputProgram =
  case lexThenParse "test-fixture.rs" inputProgram of
    Nothing => Nothing
    Just sourceFile => Just (showAstDebug sourceFile)

export
covering
parseAndListNodeIds : String -> Maybe (List Nat)
parseAndListNodeIds inputProgram =
  case lexThenParse "test-fixture.rs" inputProgram of
    Nothing => Nothing
    Just sourceFile =>
      Just (scanNodeIds (unpack (showAstDebug sourceFile)) Nothing)

||| The message the user is shown, which carries the file and the error's start,
||| paired with the span's end, which no message shows.
export
parseErrorDetails : String -> Maybe (String, (Nat, Nat))
parseErrorDetails inputProgram =
  case lexFile inputProgram of
    Left _ => Nothing
    Right tokens =>
      case parseFile "test-fixture.rs" tokens of
        Left located =>
          let errorEnd = located.span.end
          in Just (showParseError located, (errorEnd.line, errorEnd.column))
        Right _ => Nothing

export
debugTestParseError : String -> List ETest
debugTestParseError code =
  let actual = parseErrorDetails code
      name = "error details actually returned: " ++ show actual
  in test name $ actual `shouldBe` Nothing

export
debugTestParseSuccess : String -> List ETest
debugTestParseSuccess code =
  let actual = parseAndPrettyPrint code
      name = "actually returned: " ++ show actual
  in test name $ actual `shouldBe` Just "expected output"
