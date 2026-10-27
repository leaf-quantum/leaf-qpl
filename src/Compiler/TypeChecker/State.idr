module Compiler.TypeChecker.State

import Data.SortedMap

import Compiler.Type
import Compiler.TypeChecker.Data
import Compiler.TypeChecker.TcType
import Frontend.ASTData
import Frontend.Syntax.Common

%default total

--------------------------------------------------------------------------------
-- Type checker state
--------------------------------------------------------------------------------
-- Threaded through the checker in a State monad and dropped when checking
-- ends: later passes read only the TypeTables it builds.
--------------------------------------------------------------------------------

public export
data LoopContext
  = ValueLoop (Maybe TcType)                      -- `loop`: the type its break values combine to so far
  | UnitLoop                                      -- while / for: break takes no value

public export
record FunctionContext where
  constructor MkFunctionContext
  returnType     : LeafType
  declaredEffect : FunctionEffect
  loops          : List LoopContext               -- innermost first

public export
record InferenceState where                       -- per function or const initializer, emptied by writeback
  constructor MkInferenceState
  nextVariable     : Nat                          -- number of the next fresh inference variable
  variables        : SortedMap Nat VariableState
  expressionTypes  : SortedMap NodeId TcType
  patternTypes     : SortedMap NodeId TcType
  binderTypes      : SortedMap SymbolId TcType    -- locals of the function being checked
  scratchBinders   : List SymbolId
  uncomputeBinders : List SymbolId                -- bound with :=
  integerLiterals  : List (NodeId, Integer)       -- range-checked at writeback

public export
emptyInferenceState : InferenceState
emptyInferenceState = MkInferenceState 0 empty empty empty empty [] [] []

public export
record CheckerState where
  constructor MkCheckerState
  tables    : TypeTables
  function  : Maybe FunctionContext               -- Nothing while checking const initializers
  inference : InferenceState
