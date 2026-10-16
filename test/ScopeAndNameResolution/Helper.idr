module ScopeAndNameResolution.Helper

import Compiler.Desugar.Desugar
import Compiler.ScopeAndNameResolution.Data
import Compiler.ScopeAndNameResolution.Resolve
import Compiler.ScopeAndNameResolution.Validate
import Frontend.ASTData
import Frontend.ASTPhases
import Frontend.Lexer.Error
import Frontend.Lexer.Lexer
import Frontend.Parser.Error
import Frontend.Parser.Parser
import Frontend.PostParseValidation
import Frontend.Source
import Frontend.Syntax.AST
import Frontend.Token
import Text.Bounds

import Data.List
import Data.SnocList
import Data.SortedMap

%default total

public export
data FixtureError
  = LexingFailure String
  | ParsingFailure String
  | ValidationFailure (List String)
  | ResolutionFailure ResolutionError
  | InvariantFailure (List String)

public export
Show FixtureError where
  show (LexingFailure message) = "Lexing: " ++ message
  show (ParsingFailure message) = "Parsing: " ++ message
  show (ValidationFailure messages) = "Validation: " ++ show messages
  show (ResolutionFailure (UnresolvedName name span)) =
    "Resolution: unresolved " ++ name ++ " at " ++ show span.start.line ++ ":" ++ show span.start.column
  show (ResolutionFailure (DuplicateDeclaration name _ span previousSpan)) =
    "Resolution: duplicate " ++ name ++ " at " ++ show span.start.line ++ ":" ++ show span.start.column ++
    "; previous declaration at " ++ show previousSpan.start.line ++ ":" ++ show previousSpan.start.column
  show (ResolutionFailure (InaccessibleSymbol name _ span)) =
    "Resolution: inaccessible symbol " ++ name ++ " at " ++ show span.start.line ++ ":" ++ show span.start.column
  show (ResolutionFailure (BindingShadowsConstant name _ span constantSpan)) =
    "Resolution: binding " ++ name ++ " at " ++ show span.start.line ++ ":" ++ show span.start.column ++
    " shadows the constant at " ++ show constantSpan.start.line ++ ":" ++ show constantSpan.start.column
  show (InvariantFailure messages) = "Resolution invariants: " ++ show messages

-- Every successful fixture must pass table validation as well as the test's
-- semantic assertions. Failures retain the phase and original diagnostic.
export
resolveSource : String -> Either FixtureError ResolvedModule
resolveSource source = do
  tokens <- case lexFile source of
    Left err => Left (LexingFailure (renderLexerError err))
    Right tokens => Right tokens
  surface <- case parseFile "resolution-test.lf" tokens of
    Left err => Left (ParsingFailure (renderParseError err.value))
    Right surface => Right surface
  case validateSourceFile surface of
    [] => Right ()
    errors => Left (ValidationFailure (map interpolate errors))
  resolved <- case resolveCanonicalSyntax (desugarSurfaceSyntax surface) of
    Left err => Left (ResolutionFailure err)
    Right resolved => Right resolved
  case validateResolvedModule resolved of
    [] => Right resolved
    errors => Left (InvariantFailure (map show errors))

export
resolvedSource : String -> Maybe ResolvedModule
resolvedSource source = case resolveSource source of
  Left _ => Nothing
  Right resolved => Just resolved

export
checkSource : String -> (ResolvedModule -> Maybe a) -> Either String a
checkSource source inspect = case resolveSource source of
  Left err => Left (show err)
  Right resolved => case inspect resolved of
    Nothing => Left ("Unexpected resolved AST or missing table entry for: " ++ source)
    Just result => Right result

export
expectUnresolvedName : String -> Either String String
expectUnresolvedName source = case resolveSource source of
  Left (ResolutionFailure (UnresolvedName name _)) => Right name
  Left other => Left (show other)
  Right _ => Left "Expected UnresolvedName, but resolution succeeded"

export
kindText : SymbolKind -> String
kindText SymbolLocalBinding = "local"
kindText SymbolFunctionParameter = "parameter"
kindText SymbolFunction = "function"
kindText SymbolConstant = "constant"
kindText _ = "other"

export
spanKey : SourceSpan -> (String, Nat, Nat, Nat, Nat)
spanKey span = (span.file, span.start.line, span.start.column, span.end.line, span.end.column)

export
allReferences : ResolvedModule -> List SymbolReference
allReferences resolved =
  sortBy (\a, b => compare (spanKey a.occurrence.span) (spanKey b.occurrence.span)) $
    concatMap (\(_, refs) => refs <>> []) (SortedMap.toList resolved.tables.references)

export
valueReferences : ResolvedModule -> List SymbolReference
valueReferences resolved = filter isValue (allReferences resolved)
  where
    isValue : SymbolReference -> Bool
    isValue reference = case reference.role of
      ValueReference => True
      _ => False
