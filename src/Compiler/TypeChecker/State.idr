module Compiler.TypeChecker.State

import Control.Monad.State
import Data.SortedMap
import Data.SortedSet

import Compiler.TypeChecker.Data
import Compiler.TypeChecker.TcType
import Compiler.TypeChecker.Type
import Frontend.Syntax.AST
import Frontend.ASTData
import Frontend.ASTPhases
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
record TypeCheckerState where
  constructor MkTypeCheckerState
  tables        : TypeTables
  function      : Maybe FunctionContext            -- tells pass B (BodyCheck) which function it is operating inside, if any.
  inference     : InferenceState                   -- pass B's (BodyCheck) scratch space for the one body it is checking right now
  declarations  : SortedMap SymbolId ResolvedItem  -- maps each top-level item's symbol to that item's resolved AST node
  checkedBodies : SortedSet SymbolId               -- set of functions whose bodies pass B (BodyCheck) has already finished
  constExprs    : SortedMap NodeId Nat

public export
data CheckFailure
  = Blocked SymbolId                               -- needs this symbol's signature, value or checked body first
  | Failed TypeError


