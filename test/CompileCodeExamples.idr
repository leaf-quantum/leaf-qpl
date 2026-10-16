module CompileCodeExamples

import Data.String
import System.Directory
import System.File
import Text.Bounds

import Compiler.Desugar.Desugar
import Compiler.ScopeAndNameResolution.Data
import Compiler.ScopeAndNameResolution.Resolve
import Compiler.ScopeAndNameResolution.Validate
import Frontend.ASTPhases
import Frontend.Token
import Frontend.Lexer.Error
import Frontend.Lexer.Lexer
import Frontend.Parser.Error
import Frontend.Parser.Parser
import Frontend.PostParseValidation
import Frontend.Source
import Frontend.Syntax.AST

sourcePosition : SourceSpan -> String
sourcePosition span = show span.start.line ++ ":" ++ show span.start.column

resolutionErrorMessage : ResolutionError -> String
resolutionErrorMessage (UnresolvedName name span) =
  "Unresolved name '" ++ name ++ "' at " ++ sourcePosition span
resolutionErrorMessage (DuplicateDeclaration name _ current previous) =
  "Duplicate declaration '" ++ name ++ "' at " ++ sourcePosition current ++
  "; previous declaration at " ++ sourcePosition previous
resolutionErrorMessage (InaccessibleSymbol name _ span) =
  "Inaccessible symbol '" ++ name ++ "' at " ++ sourcePosition span
resolutionErrorMessage (BindingShadowsConstant name _ binder constant) =
  "Binding '" ++ name ++ "' at " ++ sourcePosition binder ++
  " shadows the constant declared at " ++ sourcePosition constant
resolutionErrorMessage (NonConstantValueInConstant name _ use local) =
  "Non-constant local '" ++ name ++ "' used at " ++ sourcePosition use ++
  " in a constant expression; declared at " ++ sourcePosition local

export
compileLeafSource : String -> String -> Either String ()
compileLeafSource programFile source =
  case lexFile source of
    Left err =>
      Left $ "In \{programFile}: " ++ renderLexerError err
    Right tokens =>
      case parseFile programFile tokens of
        Left err =>
          Left $
            "Parse error in \{programFile} at line " ++
            show err.span.start.line ++ ", column " ++
            show err.span.start.column ++ ": " ++
            renderParseError err.value
        Right surfaceAST =>
          case validateSourceFile surfaceAST of
            errors@(_ :: _) =>
              Left $
                "Validation errors in \{programFile}:\n" ++
                unlines (map interpolate errors)
            [] =>
              let canonicalAST = desugarSurfaceSyntax surfaceAST
              in case resolveCanonicalSyntax canonicalAST of
                Left err =>
                  Left $ "Resolution error in \{programFile}: " ++ resolutionErrorMessage err
                Right resolvedModule =>
                  case validateResolvedModule resolvedModule of
                    [] => Right ()
                    errors =>
                      Left $
                        "Internal scope and symbol resolution error in \{programFile}:\n" ++
                        unlines (map interpolate errors) ++
                        "This is a bug in Leaf compiler, please issue a bug report."

compileLeafFile : String -> IO (Either String ())
compileLeafFile programFile = do
  fileResult <- readFile programFile
  case fileResult of
    Left fileErr => pure $ Left $ "Failed to read \{programFile}: " ++ show fileErr
    Right source => pure $ compileLeafSource programFile source

compileLeafFiles : String -> List String -> IO (Either String ())
compileLeafFiles examplesDirectory [] = do
  putStrLn "Finished compiling all code examples."
  pure $ Right ()
compileLeafFiles examplesDirectory (fileName :: fileNames) = do
  result <- compileLeafFile $ examplesDirectory ++ "/" ++ fileName
  case result of
    Left err => pure $ Left err
    Right () => 
      do
        putStrLn $ "Successfully compiled: " ++ fileName
        compileLeafFiles examplesDirectory fileNames

export
discoverAndCompileExamples : IO (Either String ())
discoverAndCompileExamples = do
  let examplesDirectory = "examples"
  Right entries <- listDir examplesDirectory
    | Left err => pure $ Left $ "Failed to list \{examplesDirectory}: " ++ show err
  -- Example 8 demonstrates quantum conditionals, which the parser rejects
  -- explicitly until that language feature is implemented.
  let codeExampleFiles =
        filter
          (\fileName =>
            isSuffixOf ".rs" fileName &&
            fileName /= "08_deutsch_jozsa_using_quantum_conditional.rs")
          entries
  compileLeafFiles examplesDirectory (sort codeExampleFiles)
