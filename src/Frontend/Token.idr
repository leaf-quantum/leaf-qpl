-----------------------------------------------------------------------
--- Lexing produces a list of Tokens.
-----------------------------------------------------------------------

module Frontend.Token

import Data.List
import Derive.Prelude
import Derive.Finite
import Language.Reflection

%default total
%language ElabReflection

----------------------------------------------------------------------
-- Looks up the value of a `Finite` type by its `show`-style spelling.
--
-- This is the single mechanism behind every `xFromString` function below:
-- rather than hand-writing a second string -> data mapping that has to be
-- kept in sync with the data -> string one by hand (and that the compiler
-- can't check, since it matches on the open `String` type), the forward
-- direction is derived from the authoritative `showXLeaf` function plus the
-- `Finite` instance's `values` (which the elaborator derives to always list
-- every constructor). Add a constructor without giving it a `showXLeaf` case
-- and the build fails immediately -- there is no second list to forget.
----------------------------------------------------------------------
findByShow : Finite a => (a -> String) -> String -> Maybe a
findByShow showLeaf s = find (\x => showLeaf x == s) values

------------------------------------------------------
-- Primitive built-in types
------------------------------------------------------
public export
data TypPrimName
  = TypPrimAngle32
  | TypPrimAngle64
  | TypPrimBit
  | TypPrimBool
  | TypPrimF32
  | TypPrimF64
  | TypPrimI8
  | TypPrimI16
  | TypPrimI32
  | TypPrimI64
  | TypPrimI128
  | TypPrimParam
  | TypPrimU8
  | TypPrimU16
  | TypPrimU32
  | TypPrimU64
  | TypPrimU128
  | TypPrimQbit
  | TypPrimQState

%runElab derive "TypPrimName" [Eq, Finite]

public export
showTypPrimLeaf : TypPrimName -> String
showTypPrimLeaf ty =
  case ty of
    TypPrimAngle32  => "angle32"
    TypPrimAngle64  => "angle64"
    TypPrimBit      => "bit"
    TypPrimBool     => "bool"
    TypPrimF32      => "f32"
    TypPrimF64      => "f64"
    TypPrimI8       => "i8"
    TypPrimI16      => "i16"
    TypPrimI32      => "i32"
    TypPrimI64      => "i64"
    TypPrimI128     => "i128"
    TypPrimParam    => "param"
    TypPrimU8       => "u8"
    TypPrimU16      => "u16"
    TypPrimU32      => "u32"
    TypPrimU64      => "u64"
    TypPrimU128     => "u128"
    TypPrimQbit    => "qbit"
    TypPrimQState   => "qstate"

public export
implementation Show TypPrimName where
  show = showTypPrimLeaf

public export
typeFromString : String -> Maybe TypPrimName
typeFromString = findByShow showTypPrimLeaf

----------------------------------------------------------
-- BasisStateName: enumerates quantum basis states values.
-- These are globally reserved quantum state literals.
----------------------------------------------------------
public export
data BasisStateName
  = StateZero
  | StateOne
  | StatePlus
  | StateMinus
  | StatePlusI
  | StateMinusI

%runElab derive "BasisStateName" [Eq, Finite]

public export
showStateBasisLeaf : BasisStateName -> String
showStateBasisLeaf sb =
  case sb of
    StateZero   => "zero"
    StateOne    => "one"
    StatePlus   => "plus"
    StateMinus  => "minus"
    StatePlusI  => "plusi"
    StateMinusI => "minusi"

public export
implementation Show BasisStateName where
  show = showStateBasisLeaf

public export
stateBasisFromString : String -> Maybe BasisStateName
stateBasisFromString = findByShow showStateBasisLeaf

----------------------------------------------------------------------
-- Keywords: reserved words that affect syntax.
----------------------------------------------------------------------
public export
data Keyword
  = KwAdjoint
  | KwAffine
  | KwAs
  | KwBreak
  | KwCoisometry
  | KwClassical
  | KwContinue
  | KwConst
  | KwElse
  | KwEnsures
  | KwEnum
  | KwFn
  | KwFor
  | KwGeneral
  | KwIf
  | KwImpl
  | KwIn
  | KwIsometry
  | KwLet
  | KwLinear
  | KwLoop
  | KwMatch
  | KwMod
  | KwMut
  | KwPub
  | KwQenum
  | KwQelse
  | KwQif
  | KwQmatch
  | KwRequires
  | KwReturn
  | KwSelse
  | KwSif
  | KwSmatch
  | KwScratch
  | KwSelf
  | KwStruct
  | KwSupports
  | KwThen
  | KwUncompsafe
  | KwUnitary
  | KwUse
  | KwWhile

%runElab derive "Keyword" [Eq, Finite]

public export
showKeywordLeaf : Keyword -> String
showKeywordLeaf kw =
  case kw of
    KwAdjoint  => "adjoint"
    KwAffine    => "affine"
    KwAs        => "as"
    KwBreak     => "break"
    KwCoisometry => "coisometry"
    KwClassical => "classical"
    KwConst     => "const"
    KwContinue  => "continue"
    KwElse      => "else"
    KwEnsures   => "ensures"
    KwEnum      => "enum"
    KwFn        => "fn"
    KwFor       => "for"
    KwGeneral   => "general"
    KwIf        => "if"
    KwImpl      => "impl"
    KwIn        => "in"
    KwIsometry  => "isometry"
    KwLet       => "let"
    KwLinear    => "linear"
    KwLoop      => "loop"
    KwMatch     => "match"
    KwMod       => "mod"
    KwMut       => "mut"
    KwPub       => "pub"
    KwQenum     => "qenum"
    KwQelse     => "qelse"
    KwQif       => "qif"
    KwQmatch    => "qmatch"
    KwRequires  => "requires"
    KwReturn    => "return"
    KwScratch   => "scratch"
    KwSelf      => "self"
    KwSelse     => "selse"
    KwSif       => "sif"
    KwSmatch    => "smatch"
    KwStruct    => "struct"
    KwSupports  => "supports"
    KwThen      => "then"
    KwUncompsafe => "uncompsafe"
    KwUnitary   => "unitary"
    KwUse       => "use"
    KwWhile     => "while"

public export
implementation Show Keyword where
  show = showKeywordLeaf

public export
keywordFromString : String -> Maybe Keyword
keywordFromString = findByShow showKeywordLeaf

----------------------------------------------------------------------
-- Builtin: reserved intrinsic function names.
-- These cannot be shadowed by user declarations.
----------------------------------------------------------------------
public export
data Builtin
  = BuiltinBarrier
  | BuiltinCtrl
  | BuiltinOn
  | BuiltinApply
  | BuiltinBasis
  | BuiltinClean
  | BuiltinDiscard
  | BuiltinIsolated
  | BuiltinMeasr
  | BuiltinProduct
  | BuiltinQAlloc
  | BuiltinReset
  | BuiltinTensor
  | BuiltinSeparable
  | BuiltinStabilized
  | BuiltinUncompute
  | BuiltinWeaken

%runElab derive "Builtin" [Eq, Finite]

public export
showBuiltinLeaf : Builtin -> String
showBuiltinLeaf b =
  case b of
    BuiltinBarrier   => "barrier"
    BuiltinCtrl      => "ctrl"
    BuiltinOn        => "on"
    BuiltinApply     => "apply"
    BuiltinBasis     => "basis"
    BuiltinClean     => "clean"
    BuiltinDiscard   => "discard"
    BuiltinIsolated  => "isolated"
    BuiltinMeasr     => "measr"
    BuiltinProduct   => "product"
    BuiltinQAlloc    => "qalloc"
    BuiltinReset     => "reset"
    BuiltinTensor    => "tensor"
    BuiltinSeparable => "separable"
    BuiltinStabilized => "stabilized"
    BuiltinUncompute => "uncompute"
    BuiltinWeaken    => "weaken"

public export
implementation Show Builtin where
  show = showBuiltinLeaf

public export
builtinFromString : String -> Maybe Builtin
builtinFromString = findByShow showBuiltinLeaf

----------------------------------------------------------------------
-- Symbols: punctuation and operators.
----------------------------------------------------------------------
public export
data Symbol
  = SymHash                               -- #   (starts an annotation: #[...])
  | SymAmp                                -- &   (reserved; && exists too)
  | SymLParen | SymRParen                 -- ( )
  | SymLBracket | SymRBracket             -- [ ]
  | SymLBrace | SymRBrace                 -- { }
  | SymComma | SymSemi | SymColon         -- , ; :
  | SymDot                                -- .
  | SymBang                               -- !
  | SymEq                                 -- =
  | SymPlus | SymMinus | SymStar | SymSlash | SymPercent -- + - * / %
  | SymPlusEq | SymMinusEq | SymStarEq | SymSlashEq | SymPercentEq
  | SymWalrusEq                           --  :=
  | SymGt | SymGe | SymLt | SymLe         -- >, >=, <, <=
  | SymEqEq | SymNotEq                    -- ==, !=
  | SymAndAnd | SymOrOr                   -- && and ||
  | SymDotDot | SymDotDotEq               -- .. and ..=
  | SymDoubleColon                        -- ::
  | SymPipe | SymCaret                    -- | and ^
  | SymArrow                              -- ->
  | SymFatArrow                           -- =>  (match arm separator)
  | SymShl | SymShlEq | SymShr | SymShrEq -- <<, <<=, >>, >>=
  | SymAndEq | SymOrEq | SymCaretEq       -- "&=", "|=", "^="

%runElab derive "Symbol" [Eq, Finite]

public export
showSymbolLeaf : Symbol -> String
showSymbolLeaf sym =
  case sym of
    SymHash        => "#"
    SymAmp         => "&"
    SymLParen      => "("
    SymRParen      => ")"
    SymLBracket    => "["
    SymRBracket    => "]"
    SymLBrace      => "{"
    SymRBrace      => "}"
    SymComma       => ","
    SymSemi        => ";"
    SymColon       => ":"
    SymDot         => "."
    SymBang        => "!"
    SymEq          => "="
    SymPlus        => "+"
    SymMinus       => "-"
    SymStar        => "*"
    SymSlash       => "/"
    SymPercent     => "%"
    SymPlusEq      => "+="
    SymMinusEq     => "-="
    SymStarEq      => "*="
    SymSlashEq     => "/="
    SymPercentEq   => "%="
    SymWalrusEq    => ":="
    SymGt          => ">"
    SymGe          => ">="
    SymLt          => "<"
    SymLe          => "<="
    SymEqEq        => "=="
    SymNotEq       => "!="
    SymAndAnd      => "&&"
    SymOrOr        => "||"
    SymDotDot      => ".."
    SymDotDotEq    => "..="
    SymDoubleColon => "::"
    SymPipe        => "|"
    SymCaret       => "^"
    SymArrow       => "->"
    SymFatArrow    => "=>"
    SymShl         => "<<"
    SymShlEq       => "<<="
    SymShr         => ">>"
    SymShrEq       => ">>="
    SymAndEq       => "&="
    SymOrEq        => "|="
    SymCaretEq     => "^="

public export
implementation Show Symbol where
  show = showSymbolLeaf

----------------------------------------------------------------------------------------------------------
-- Convenience table for consumers that need every symbol spelling. It is derived from `showSymbolLeaf`
-- and `Finite Symbol`, so there is exactly one hand-written spelling per symbol. The lexer generates its
-- rules directly with ilex's `vals` helper from the same two sources of truth.
----------------------------------------------------------------------------------------------------------
public export
symbolTable : List (String, Symbol)
symbolTable = map (\sym => (showSymbolLeaf sym, sym)) values

----------------------------------------------------------------------
-- Token:
--   TokIdent "x"
--   TokIntLitRaw "123"
--   TokFloatLitRaw "3.14"
--   TokByteLitRaw "b'a'"
--   TokByteStringLitRaw "b\"hello\""
--   TokBasisStringLitRaw "bs\"01+-iI\""
--   TokStringLitRaw "\"Hello\""
--   TokOuterDoc "/// docs for following item"
--   TokInnerDoc "//! docs for enclosing item"
--   TokBoolLit True
--   TokStateLit StateZero
--   TokKw KwLet
--   TokTypPrim TypPrimI32
--   TokSym SymPlusEq
--   TokBuiltin BuiltinMeasr
--   TokUnderscore "_"
--   TokEOF
----------------------------------------------------------------------
public export
data Token
  = TokIdent             String
  | TokIntLitRaw         String
  | TokFloatLitRaw       String
  | TokByteLitRaw        String
  | TokByteStringLitRaw  String
  | TokBasisStringLitRaw String
  | TokStringLitRaw      String
  | TokOuterDoc          String   -- /// line  or  /** … */ block: documents the item that FOLLOWS
  | TokInnerDoc          String   -- //! line  or  /*! … */ block: documents the ENCLOSING item
  | TokBoolLit           Bool
  | TokStateLit          BasisStateName
  | TokKw                Keyword
  | TokTypPrim           TypPrimName
  | TokSym               Symbol
  | TokBuiltin           Builtin
  | TokUnderscore
  | TokEOF

%runElab derive "Token" [Show, Eq]

public export
Interpolation Token where
  interpolate token =
    case token of
      TokIdent rawText             => rawText
      TokIntLitRaw rawText         => rawText
      TokFloatLitRaw rawText       => rawText
      TokByteLitRaw rawText        => rawText
      TokByteStringLitRaw rawText  => rawText
      TokBasisStringLitRaw rawText => rawText
      TokStringLitRaw rawText      => rawText
      TokOuterDoc rawText          => rawText
      TokInnerDoc rawText          => rawText
      TokBoolLit True              => "true"
      TokBoolLit False             => "false"
      TokStateLit state            => showStateBasisLeaf state
      TokKw keyword                => showKeywordLeaf keyword
      TokTypPrim typ               => showTypPrimLeaf typ
      TokSym symbol                => showSymbolLeaf symbol
      TokBuiltin builtin           => showBuiltinLeaf builtin
      TokUnderscore                => "_"
      TokEOF                       => "end of input"

public export
describeToken : Token -> String
describeToken (TokIdent name)             = "identifier " ++ show name
describeToken (TokIntLitRaw text)         = "raw integer literal `" ++ text ++ "`"
describeToken (TokFloatLitRaw text)       = "raw float literal `" ++ text ++ "`"
describeToken (TokByteLitRaw text)        = "raw byte literal `" ++ text ++ "`"
describeToken (TokByteStringLitRaw text)  = "raw byte string literal `" ++ text ++ "`"
describeToken (TokBasisStringLitRaw text) = "raw basis string literal `" ++ text ++ "`"
describeToken (TokStringLitRaw text)      = "raw string literal `" ++ text ++ "`"
describeToken (TokOuterDoc text)          = "outer doc comment " ++ show text
describeToken (TokInnerDoc text)          = "inner doc comment " ++ show text
describeToken (TokBoolLit True)           = "boolean literal true"
describeToken (TokBoolLit False)          = "boolean literal false"
describeToken (TokStateLit state)         = "state literal " ++ show state
describeToken (TokKw keyword)             = "keyword " ++ show keyword
describeToken (TokTypPrim typ)            = "primitive type " ++ show typ
describeToken (TokSym symbol)             = "symbol " ++ show symbol
describeToken (TokBuiltin builtin)        = "builtin " ++ show builtin
describeToken TokUnderscore               = "underscore"
describeToken TokEOF                      = "end of input"

----------------------------------------------------------------------
-- Boolean literals. Only two spellings, spelled out directly rather than
-- routed through `findByShow`: Leaf's `true`/`false` spelling differs from
-- Idris's own `Show Bool` (`True`/`False`), so reusing that mechanism here
-- would need its own `showBoolLiteral` anyway, for no less code overall.
----------------------------------------------------------------------
public export
boolFromString : String -> Maybe Bool
boolFromString s =
  case s of
    "true"  => Just True
    "false" => Just False
    _       => Nothing

---------------------------------------------------------------------
-- single authoritative classification order for identifier-like text:
-- bools, keywords, types, state basis, builtins, identifiers
---------------------------------------------------------------------
public export
tokenFromIdentLike : String -> Token
tokenFromIdentLike s =
  case s of
    "_" => TokUnderscore
    _ =>
      case boolFromString s of
        Just b => TokBoolLit b
        Nothing =>
          case keywordFromString s of
            Just kw => TokKw kw
            Nothing =>
              case typeFromString s of
                Just ty => TokTypPrim ty
                Nothing =>
                  case stateBasisFromString s of
                    Just st => TokStateLit st
                    Nothing =>
                      case builtinFromString s of
                        Just bi => TokBuiltin bi
                        Nothing => TokIdent s
