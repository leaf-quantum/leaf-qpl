module Run

import System

import CompileCodeExamples
import CompileCodeExamplesTest
import Desugarer.DesugaringTest
import Lexer.LexerTest
import PostParseValidator.PostParseValidationTest
import Parser.ExpressionParseTest
import Parser.FunctionParseTest
import Parser.TopModuleParseTest
import ScopeAndNameResolution.ValidationTest
import ScopeAndNameResolution.ResolveTest
import ScopeAndNameResolution.PreludeTest

main : IO ()
main = do
  runLexerTests
  runExpressionParseTests
  runFunctionParseTests
  runTopModuleParseTests
  runPostParseValidationTests
  runDesugaringTests
  runSymbolAndScopeResolutionTests
  runPreludeFunctionsResolutionTests
  runResolutionValidationTests
  runCompileCodeExamplesTests
  Right () <- discoverAndCompileExamples
    | Left err => do
        putStrLn err
        exitFailure
  putStrLn "All tests completed."
