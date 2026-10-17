module Main

import Data.List
import Data.String
import Text.Bounds
import System
import System.File

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
import Compiler.Validation.PostParseValidation
import Frontend.Source
import Frontend.Syntax.AST
import Frontend.Utils.ASTDebugPrinter
import Frontend.Utils.ASTPrettyPrinter

%default total

isOneWord : String -> Bool
isOneWord fileName =
  fileName /= "" &&
  not (any isSpace (unpack fileName))

isValidLeafFileName : String -> Bool
isValidLeafFileName fileName =
  isOneWord fileName &&
  (isSuffixOf ".lf" fileName || isSuffixOf ".rs" fileName)

showParseError : Located ParseError -> String
showParseError err =
  let errorFile = err.span.file
      errorSpanStart = err.span.start
  in "Parse error at: "
      ++ errorFile
      ++ ", at line: "
      ++ show errorSpanStart.line
      ++ ", at column: "
      ++ show errorSpanStart.column
      ++ ", with message: "
      ++ renderParseError err.value

showSourceSpan : SourceSpan -> String
showSourceSpan sspan = "file: '\{sspan.file}' at line: '\{show sspan.start.line}' and column: '\{show sspan.start.column}'"

showResolutionError : ResolutionError -> String
showResolutionError (UnresolvedName name sourceSpan) =
  "Could not find a matching declaration for this name: '\{name}' in '\{showSourceSpan sourceSpan}'."
showResolutionError (DuplicateDeclaration name symbolIds sourceSpan previousSpan) =
  "A duplicate declaration for name: '\{name}' declared in '\{showSourceSpan sourceSpan}' was found; the previous declaration is in '\{showSourceSpan previousSpan}'."
showResolutionError (InaccessibleSymbol name _ sourceSpan) =
  "At current location '\{showSourceSpan sourceSpan}' the name: '\{name}' is not publicly accessible."
showResolutionError (BindingShadowsConstant name _ sourceSpan constantSpan) =
  "The mutable binding for name: '\{name}' in '\{showSourceSpan sourceSpan}' cannot shadow the constant declared in '\{showSourceSpan constantSpan}'."
showResolutionError (LocalValueUsedAsConstant name _ sourceSpan localSpan) =
  "The local: '\{name}' used in '\{showSourceSpan sourceSpan}' is not a constant and cannot be used in an array length or repeat count; it is declared in '\{showSourceSpan localSpan}'."

printAstAndProgram : PhasePretty phase => SourceFile phase -> IO ()
printAstAndProgram astTree = do
  putStrLn "AST Nodes:"
  putStrLn $ assert_total showAstDebug astTree
  putStrLn "Pretty Printed Program:"
  putStrLn $ "Parsed program:\n" ++ showSourceFileStrict astTree

export
compileSource : (fileName : String) -> (source : String) -> Either String ResolvedModule
compileSource fileName source =
  case lexFile source of
    Left err => Left $ renderLexerError err
    Right tokens =>
      case parseFile fileName tokens of
        Left err => Left $ showParseError err
        Right surfaceAst =>
          case validateSourceFile surfaceAst of
            errors@(_ :: _) =>
              Left $ joinBy "\n" ("Validation errors:" :: map interpolate errors)
            [] =>
              let canonicalAst = desugarSurfaceSyntax surfaceAst
              in case resolveCanonicalSyntax canonicalAst of
                Left resolutionError => Left $ showResolutionError resolutionError
                Right resolvedModule =>
                  case validateResolvedModule resolvedModule of
                    errors@(_ :: _) =>
                      Left $ joinBy "\n" $
                        "Internal scope and symbol resolution error:" ::
                        map interpolate errors ++
                        ["This is a bug in Leaf compiler, please file a bug report."]
                    [] => Right resolvedModule

main : IO ()
main = do
    putStrLn "Hello from Leaf!"
    (program :: args) <- getArgs
      | [] => putStrLn "impossible: empty argv"
    case args of
      [fileName] => case isValidLeafFileName fileName of
        False => putStrLn "Invalid filename: expected an .lf or .rs file."
        True => do
          fileResult <- assert_total readFile fileName
          case fileResult of
            Left fileErr => putStrLn $ "Failed to read \{fileName}: " ++ show fileErr
            Right sampleProgram =>
              case compileSource fileName sampleProgram of
                Left message => putStrLn message
                Right _ => pure ()

      _ => putStrLn "Please provide exactly one input .lf or .rs file."
