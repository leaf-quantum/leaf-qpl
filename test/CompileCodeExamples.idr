module CompileCodeExamples

import Data.String
import System.Directory
import System.File

import Compiler.ScopeAndNameResolution.Data
import Main

compileLeafFile : String -> IO (Either String ())
compileLeafFile programFile = do
  fileResult <- readFile programFile
  case fileResult of
    Left fileErr => pure $ Left $ "Failed to read \{programFile}: " ++ show fileErr
    Right source => pure $ map (const ()) (compileSource programFile source)

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
