module Desugarer.Helper

import Text.Bounds

import Compiler.Desugar.Desugar
import Frontend.ASTData
import Frontend.ASTPhases
import Frontend.Lexer.Error
import Frontend.Lexer.Lexer
import Frontend.Parser.Error
import Frontend.Parser.Parser
import Frontend.Source
import Frontend.Syntax.AST
import Frontend.Syntax.Common
import Frontend.Syntax.Type
import Frontend.Utils.ASTPrettyPrinter
import Frontend.Token

%default total

export
lexParseThenDesugar : String -> String -> Maybe CanonicalSourceFile
lexParseThenDesugar fileName inputProgram =
  case lexFile inputProgram of
    Left _ => Nothing
    Right tokens => case parseFile fileName tokens of
      Left _ => Nothing
      Right surfaceSourceFile => Just (desugarSurfaceSyntax surfaceSourceFile)

export
desugarAndPrettyPrint : String -> Maybe String
desugarAndPrettyPrint inputProgram =
  map showSourceFileStrict (lexParseThenDesugar "test-fixture.rs" inputProgram)

||| Start and end (line, column) of each multiplicity qualifier at an owned
||| position of the first function's first `let` annotation, after desugaring.
export
firstLetTypeQualifierSpans : String -> Maybe (List ((Nat, Nat), (Nat, Nat)))
firstLetTypeQualifierSpans inputProgram = do
  MkAstNode _ _ (MkSourceFileNode _ items) <- lexParseThenDesugar "test-fixture.rs" inputProgram
  MkAstNode _ _ (ItemFunction declaration) :: _ <- Just items
    | _ => Nothing
  let MkAstNode _ _ (MkBlockNode _ statements _) = declaration.functionBody
  MkAstNode _ _ (StatementLet (MkLetBindingNode _ _ (Just annotation) _)) :: _ <- Just statements
    | _ => Nothing
  Just (map (bounds . (.astInfo.span)) (mapMaybe positionQualifier (ownedPositions annotation)))
  where
    bounds : SourceSpan -> ((Nat, Nat), (Nat, Nat))
    bounds span = ((span.start.line, span.start.column), (span.end.line, span.end.column))
