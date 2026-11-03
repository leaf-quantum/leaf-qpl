module Compiler.TypeChecker.PreludeSignatures

import Compiler.TypeChecker.Data

%default total

public export
preludeSymbolType : String -> InferredType
preludeSymbolType symbolName = ?preludeValueTypeH
