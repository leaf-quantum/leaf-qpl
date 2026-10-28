module Lexer.LexerTest

import Text.Bounds
import Test.Simple

import Frontend.Token
import Frontend.Lexer.Error
import Frontend.Lexer.Lexer

%default total

tokenValues : Either (Bounded LexerError) (List (Bounded Token)) -> Either LexerError (List Token)
tokenValues (Left boundedError) =
  Left boundedError.val
tokenValues (Right boundedTokens) =
  Right (map val boundedTokens)

lexTokenValues : String -> Either LexerError (List Token)
lexTokenValues input =
  tokenValues (lexFile input)

lexErrorHasBounds : String -> Maybe Bool
lexErrorHasBounds input =
  case lexFile input of
    Left boundedError =>
      case boundedError.bounds of
        NoBounds => Just False
        _ => Just True

    Right _ =>
      Nothing

lexErrorBounds : String -> Maybe Bounds
lexErrorBounds input =
  case lexFile input of
    Left boundedError => Just boundedError.bounds
    Right _ => Nothing

finalEofHasZeroWidthBounds : String -> Maybe Bool
finalEofHasZeroWidthBounds input =
  case lexFile input of
    Left _ =>
      Nothing

    Right boundedTokens =>
      finalEofBounds boundedTokens
  where
    finalEofBounds : List (Bounded Token) -> Maybe Bool
    finalEofBounds [] =
      Nothing

    finalEofBounds (boundedToken :: []) =
      case boundedToken.val of
        TokEOF =>
          case boundedToken.bounds of
            BS start end => Just (start == end)
            NoBounds => Just False

        _ =>
          Nothing

    finalEofBounds (_ :: remainingTokens) =
      finalEofBounds remainingTokens

identTokens : List String -> List Token
identTokens names =
  map TokIdent names ++ [TokEOF]

symbolTokens : List Symbol -> List Token
symbolTokens symbols =
  map TokSym symbols ++ [TokEOF]

spaceSeparated : List String -> String
spaceSeparated [] = ""
spaceSeparated (name :: []) = name
spaceSeparated (name :: remainingNames) =
  name ++ " " ++ spaceSeparated remainingNames

export
runLexerTests : IO ()
runLexerTests = runTests $ Test.do
  ------------------------------------------------------------
  -- Whitespace, comments, and documentation comments.
  ------------------------------------------------------------
  test "empty input lexes as just end of file" $
    lexTokenValues "" `shouldBe` Right [TokEOF]

  test "end of file token has zero-width bounds" $
    finalEofHasZeroWidthBounds "fn\n" `shouldBe` Just True

  test "lexer errors have a human-readable bounded rendering" $
    renderLexerError
      (B LexUnterminatedStringLiteral (BS (P 0 1) (P 0 4))) `shouldBe`
        "Lexer error at 1:2--1:5: Unterminated string literal"

  test "whitespace is skipped" $
    lexTokenValues " \t\n\r\n\rfn" `shouldBe`
      Right [TokKw KwFn, TokEOF]

  test "normal line comments are skipped" $
    lexTokenValues "let // comment\nx" `shouldBe`
      Right [TokKw KwLet, TokIdent "x", TokEOF]

  test "normal nested block comments are skipped" $
    lexTokenValues "let /* outer /* inner */ ok */ x" `shouldBe`
      Right [TokKw KwLet, TokIdent "x", TokEOF]

  test "multi-line nested block comments with blank lines are skipped" $
    lexTokenValues
      ( "let /*\n"
     ++ "  This is an outer block comment.\n"
     ++ "\n"
     ++ "  /*\n"
     ++ "      This is a nested block comment.\n"
     ++ "      Leaf allows this.\n"
     ++ "  */\n"
     ++ "\n"
     ++ "  Back in the outer comment.\n"
     ++ "*/ x"
      ) `shouldBe` Right [TokKw KwLet, TokIdent "x", TokEOF]

  test "outer line docs are emitted" $
    lexTokenValues "/// docs\nfn" `shouldBe`
      Right [TokOuterDoc "/// docs", TokKw KwFn, TokEOF]

  test "inner line docs are emitted" $
    lexTokenValues "//! docs\nfn" `shouldBe`
      Right [TokInnerDoc "//! docs", TokKw KwFn, TokEOF]

  test "outer block docs are emitted" $
    lexTokenValues "/** docs */fn" `shouldBe`
      Right [TokOuterDoc "/** docs */", TokKw KwFn, TokEOF]

  test "inner block docs are emitted" $
    lexTokenValues "/*! docs */fn" `shouldBe`
      Right [TokInnerDoc "/*! docs */", TokKw KwFn, TokEOF]

  test "outer block doc keeps embedded newlines in its raw text" $
    lexTokenValues "/** line one\n    line two */fn" `shouldBe`
      Right [TokOuterDoc "/** line one\n    line two */", TokKw KwFn, TokEOF]

  test "nested plain comment inside an outer block doc is captured verbatim" $
    lexTokenValues "/** outer /* nested */ done */fn" `shouldBe`
      Right
        [ TokOuterDoc "/** outer /* nested */ done */"
        , TokKw KwFn, TokEOF
        ]

  test "nested plain comment inside an inner block doc is captured verbatim" $
    lexTokenValues "/*! inner /* nested */ done */fn" `shouldBe`
      Right
        [ TokInnerDoc "/*! inner /* nested */ done */"
        , TokKw KwFn, TokEOF
        ]

  test "four slash line comment is normal comment" $
    lexTokenValues "//// docs\nfn" `shouldBe` Right [TokKw KwFn, TokEOF]

  test "slash slash slash bang is outer line doc" $
    lexTokenValues "///!\nfn" `shouldBe`
      Right [TokOuterDoc "///!", TokKw KwFn, TokEOF]

  test "slash slash bang slash is inner line doc" $
    lexTokenValues "//!/\nfn" `shouldBe`
      Right [TokInnerDoc "//!/", TokKw KwFn, TokEOF]

  test "bare triple-slash line is still an outer doc token" $
    lexTokenValues "///\nfn" `shouldBe`
      Right [TokOuterDoc "///", TokKw KwFn, TokEOF]

  test "four-slash-bang line is still a normal comment" $
    lexTokenValues "////! docs\nfn" `shouldBe`
      Right [TokKw KwFn, TokEOF]

  test "block comments can contain slash-slash doc-looking text" $
    lexTokenValues "/* /// not-a-doc */fn" `shouldBe`
      Right [TokKw KwFn, TokEOF]

  test "empty slash-star-star-slash block comment is skipped" $
    lexTokenValues "/**/fn" `shouldBe` Right [TokKw KwFn, TokEOF]

  test "slash-star-star-star-slash block comment is skipped" $
    lexTokenValues "/***/fn" `shouldBe` Right [TokKw KwFn, TokEOF]

  test "four-star block comment is skipped regardless of star-run length" $
    lexTokenValues "/****/fn" `shouldBe` Right [TokKw KwFn, TokEOF]

  test "three-star block comment with content is not an outer doc" $
    lexTokenValues "/*** docs */fn" `shouldBe`
      Right [TokKw KwFn, TokEOF]

  test "four-star block comment with content is not an outer doc" $
    lexTokenValues "/**** docs */fn" `shouldBe`
      Right [TokKw KwFn, TokEOF]

  test "banner-style block comment is not an outer doc" $
    lexTokenValues "/***\n * banner\n */fn" `shouldBe`
      Right [TokKw KwFn, TokEOF]

  test "inner block doc can be empty" $
    lexTokenValues "/*!*/fn" `shouldBe`
      Right [TokInnerDoc "/*!*/", TokKw KwFn, TokEOF]

  test "unterminated block comment is a lexer error" $
    lexTokenValues "/* nope" `shouldBe` Left LexUnterminatedBlockComment

  test "unterminated block comment error has bounds" $
    lexErrorHasBounds "/* nope" `shouldBe` Just True

  test "unterminated nested block comment is still a lexer error" $
    lexTokenValues "/* outer /* inner" `shouldBe` Left LexUnterminatedBlockComment

  test "unterminated nested block comment error has bounds" $
    lexErrorHasBounds "/* outer /* inner" `shouldBe` Just True

  test "unterminated outer block doc comment is a lexer error" $
    lexTokenValues "/** unterminated" `shouldBe` Left LexUnterminatedBlockComment

  test "block comment truncated right after two stars is unterminated" $
    lexTokenValues "/**" `shouldBe` Left LexUnterminatedBlockComment

  test "block comment truncated right after three stars is unterminated" $
    lexTokenValues "/***" `shouldBe` Left LexUnterminatedBlockComment

  test "block comment truncated right after four stars is unterminated" $
    lexTokenValues "/****" `shouldBe` Left LexUnterminatedBlockComment

  test "bare slash-star with nothing else is unterminated" $
    lexTokenValues "/*" `shouldBe` Left LexUnterminatedBlockComment

  test "triple-nested block comments are skipped" $
    lexTokenValues "let /* one /* two /* three */ two */ one */ x" `shouldBe`
      Right [TokKw KwLet, TokIdent "x", TokEOF]

  test "tabs remain inside line comments" $
    [ lexTokenValues "let // hidden\tx\ny"
    , lexTokenValues "/// doc\tcontinued\nfn"
    , lexTokenValues "//! doc\tcontinued\nfn"
    ] `shouldBe`
      [ Right [TokKw KwLet, TokIdent "y", TokEOF]
      , Right [TokOuterDoc "/// doc\tcontinued", TokKw KwFn, TokEOF]
      , Right [TokInnerDoc "//! doc\tcontinued", TokKw KwFn, TokEOF]
      ]

  test "tabs remain inside block comments" $
    [ lexTokenValues "let /* hidden\tx */ y"
    , lexTokenValues "/** doc\tcontinued */fn"
    , lexTokenValues "/*! doc\tcontinued */fn"
    ] `shouldBe`
      [ Right [TokKw KwLet, TokIdent "y", TokEOF]
      , Right [TokOuterDoc "/** doc\tcontinued */", TokKw KwFn, TokEOF]
      , Right [TokInnerDoc "/*! doc\tcontinued */", TokKw KwFn, TokEOF]
      ]

  test "CRLF line ending terminates a normal line comment" $
    lexTokenValues "let // comment\r\nx" `shouldBe`
      Right [TokKw KwLet, TokIdent "x", TokEOF]

  test "CRLF line ending terminates an outer doc line comment" $
    lexTokenValues "/// docs\r\nfn" `shouldBe`
      Right [TokOuterDoc "/// docs", TokKw KwFn, TokEOF]

  test "a bare CR terminates line comments and is then skipped as whitespace" $
    [ lexTokenValues "let // hidden\rx"
    , lexTokenValues "/// docs\rfn"
    ] `shouldBe`
      [ Right [TokKw KwLet, TokIdent "x", TokEOF]
      , Right [TokOuterDoc "/// docs", TokKw KwFn, TokEOF]
      ]

  test "bare CR advances token and EOF coordinates" $
    lexFile "a\rb" `shouldBe`
      Right
        [ B (TokIdent "a") (BS (P 0 0) (P 0 0))
        , B (TokIdent "b") (BS (P 1 0) (P 1 0))
        , B TokEOF (BS (P 1 1) (P 1 1))
        ]

  test "CRLF coordinates are unchanged" $
    lexFile "a\r\nb" `shouldBe`
      Right
        [ B (TokIdent "a") (BS (P 0 0) (P 0 0))
        , B (TokIdent "b") (BS (P 1 0) (P 1 0))
        , B TokEOF (BS (P 1 1) (P 1 1))
        ]

  test "bare CR in a block doc is preserved while advancing coordinates" $
    lexFile "/** a\rb */fn" `shouldBe`
      Right
        [ B (TokOuterDoc "/** a\rb */") (BS (P 0 0) (P 1 3))
        , B (TokKw KwFn) (BS (P 1 4) (P 1 5))
        , B TokEOF (BS (P 1 6) (P 1 6))
        ]

  test "an error after bare CR starts on the next line" $
    lexErrorBounds "// c\r@" `shouldBe`
      Just (BS (P 1 0) (P 1 0))

  test "a normal line comment may run to end of input" $
    lexTokenValues "let // trailing comment" `shouldBe`
      Right [TokKw KwLet, TokEOF]

  test "CRLF line endings inside an ordinary block comment are skipped" $
    lexTokenValues "let /* comment\r\n more */ x" `shouldBe`
      Right [TokKw KwLet, TokIdent "x", TokEOF]

  test "outer block doc keeps an embedded CRLF line break in its raw text" $
    lexTokenValues "/** line one\r\n    line two */fn" `shouldBe`
      Right [TokOuterDoc "/** line one\r\n    line two */", TokKw KwFn, TokEOF]

  test "a nested comment opener that looks like a doc opener does not change the outer plain comment's mode" $
    lexTokenValues "let /* outer /** looks doc */ still plain */ x" `shouldBe`
      Right [TokKw KwLet, TokIdent "x", TokEOF]

  ------------------------------------------------------------
  -- Identifiers and reserved words.
  ------------------------------------------------------------
  test "underscore alone is a wildcard token" $
    lexTokenValues "_" `shouldBe` Right [TokUnderscore, TokEOF]

  test "underscore-prefixed names are identifiers" $
    lexTokenValues "_x" `shouldBe` Right [TokIdent "_x", TokEOF]

  test "apostrophe remains part of identifiers" $
    lexTokenValues "foo' fn'" `shouldBe`
      Right [TokIdent "foo'", TokIdent "fn'", TokEOF]

  test "Unicode letters are valid identifier start and continuation characters" $
    lexTokenValues "café Ω θ_variable" `shouldBe`
      Right
        [ TokIdent "café", TokIdent "Ω", TokIdent "θ_variable"
        , TokEOF
        ]

  test "Unicode decimal digits continue identifiers" $
    lexTokenValues "x०१ n१" `shouldBe`
      Right [TokIdent "x०१", TokIdent "n१", TokEOF]

  test "reserved prefixes remain identifiers when extended" $
    lexTokenValues "truex zerox minusi1 qalloc'" `shouldBe`
      Right
        [ TokIdent "truex", TokIdent "zerox"
        , TokIdent "minusi1", TokIdent "qalloc'"
        , TokEOF
        ]

  test "boolean literals are boolean literal tokens" $
    lexTokenValues "false true" `shouldBe`
      Right [TokBoolLit False, TokBoolLit True, TokEOF]

  test "keywords are keyword tokens" $
    lexTokenValues "adjoint affine as break classical coisometry const continue else ensures enum fn for general if impl in isometry let linear loop match mod mut pub qif qelse qenum qmatch requires return scratch self selse sif smatch struct supports then unitary uncompsafe use while" `shouldBe`
      Right
        [ TokKw KwAdjoint, TokKw KwAffine, TokKw KwAs, TokKw KwBreak
        , TokKw KwClassical, TokKw KwCoisometry, TokKw KwConst
        , TokKw KwContinue, TokKw KwElse, TokKw KwEnsures, TokKw KwEnum
        , TokKw KwFn, TokKw KwFor, TokKw KwGeneral, TokKw KwIf
        , TokKw KwImpl, TokKw KwIn, TokKw KwIsometry, TokKw KwLet
        , TokKw KwLinear, TokKw KwLoop, TokKw KwMatch, TokKw KwMod
        , TokKw KwMut, TokKw KwPub, TokKw KwQif, TokKw KwQelse
        , TokKw KwQenum, TokKw KwQmatch, TokKw KwRequires
        , TokKw KwReturn, TokKw KwScratch, TokKw KwSelf, TokKw KwSelse
        , TokKw KwSif, TokKw KwSmatch, TokKw KwStruct, TokKw KwSupports
        , TokKw KwThen, TokKw KwUnitary, TokKw KwUncompsafe
        , TokKw KwUse, TokKw KwWhile, TokEOF
        ]

  test "keyword matching is case-sensitive" $
    lexTokenValues "Fn fn FN" `shouldBe`
      Right [TokIdent "Fn", TokKw KwFn, TokIdent "FN", TokEOF]

  test "literal, type, state, and builtin classification is case-sensitive" $
    lexTokenValues "True False Zero One Qbit QState Qalloc Measr" `shouldBe`
      Right
        [ TokIdent "True", TokIdent "False"
        , TokIdent "Zero", TokIdent "One"
        , TokIdent "Qbit", TokIdent "QState"
        , TokIdent "Qalloc", TokIdent "Measr"
        , TokEOF
        ]

  test "basis and byte literal prefixes remain identifiers when extended" $
    lexTokenValues "bs_data byte_string b_value" `shouldBe`
      Right
        [ TokIdent "bs_data", TokIdent "byte_string", TokIdent "b_value"
        , TokEOF
        ]

  test "primitive types are primitive type tokens" $
    lexTokenValues "angle32 angle64 bit bool f32 f64 i8 i16 i32 i64 i128 param u8 u16 u32 u64 u128 qbit qstate" `shouldBe`
      Right
        [ TokTypPrim TypPrimAngle32, TokTypPrim TypPrimAngle64
        , TokTypPrim TypPrimBit, TokTypPrim TypPrimBool
        , TokTypPrim TypPrimF32, TokTypPrim TypPrimF64
        , TokTypPrim TypPrimI8, TokTypPrim TypPrimI16
        , TokTypPrim TypPrimI32, TokTypPrim TypPrimI64
        , TokTypPrim TypPrimI128, TokTypPrim TypPrimParam
        , TokTypPrim TypPrimU8, TokTypPrim TypPrimU16
        , TokTypPrim TypPrimU32, TokTypPrim TypPrimU64
        , TokTypPrim TypPrimU128, TokTypPrim TypPrimQbit
        , TokTypPrim TypPrimQState, TokEOF
        ]

  test "Param is prelude identifier while param is primitive type" $
    lexTokenValues "Param param" `shouldBe`
      Right [TokIdent "Param", TokTypPrim TypPrimParam, TokEOF]

  test "state literals are state literal tokens" $
    lexTokenValues "zero one plus minus plusi minusi" `shouldBe`
      Right
        [ TokStateLit StateZero, TokStateLit StateOne
        , TokStateLit StatePlus, TokStateLit StateMinus
        , TokStateLit StatePlusI, TokStateLit StateMinusI
        , TokEOF
        ]

  test "non-shadowable builtins are builtin tokens" $
    lexTokenValues "barrier ctrl on apply basis clean discard isolated measr product qalloc reset tensor separable stabilized uncompute weaken" `shouldBe`
      Right
        [ TokBuiltin BuiltinBarrier, TokBuiltin BuiltinCtrl
        , TokBuiltin BuiltinOn, TokBuiltin BuiltinApply
        , TokBuiltin BuiltinBasis, TokBuiltin BuiltinClean
        , TokBuiltin BuiltinDiscard, TokBuiltin BuiltinIsolated
        , TokBuiltin BuiltinMeasr, TokBuiltin BuiltinProduct
        , TokBuiltin BuiltinQAlloc, TokBuiltin BuiltinReset
        , TokBuiltin BuiltinTensor, TokBuiltin BuiltinSeparable
        , TokBuiltin BuiltinStabilized, TokBuiltin BuiltinUncompute
        , TokBuiltin BuiltinWeaken, TokEOF
        ]

  test "prelude math names and gate names are identifiers" $
    let names =
          [ "Param", "phase", "turns", "abs", "acos", "asin", "atan"
          , "ceil", "cos", "exp", "floor", "ln", "log2", "log10"
          , "max", "min", "round", "sin", "sqrt", "tan"
          , "I", "X", "Y", "Z", "H", "S", "SDG", "T", "TDG"
          , "SX", "SXDG", "RX", "RY", "RZ", "U1", "U2", "U3"
          , "CNOT", "CX", "CY", "CZ", "CS", "CSDG", "CT", "CTDG"
          , "CSX", "CSXDG", "CRX", "CRY", "CRZ", "CU1", "CU2"
          , "CU3", "SWAP", "RXX", "RYY", "RZZ", "CCX", "CSWAP"
          , "GPI", "GPI2", "MS", "ZZ"
          ]
     in lexTokenValues (spaceSeparated names) `shouldBe` Right (identTokens names)

  test "reserved callable names tokenize structurally when called" $
    lexTokenValues "adjoint() ctrl().on().apply()" `shouldBe`
      Right
        [ TokKw KwAdjoint, TokSym SymLParen, TokSym SymRParen
        , TokBuiltin BuiltinCtrl, TokSym SymLParen, TokSym SymRParen
        , TokSym SymDot, TokBuiltin BuiltinOn
        , TokSym SymLParen, TokSym SymRParen
        , TokSym SymDot, TokBuiltin BuiltinApply
        , TokSym SymLParen, TokSym SymRParen
        , TokEOF
        ]

  test "adjoint block form starts with keyword then brace" $
    lexTokenValues "adjoint { H(&q); }" `shouldBe`
      Right
        [ TokKw KwAdjoint, TokSym SymLBrace
        , TokIdent "H", TokSym SymLParen, TokSym SymAmp, TokIdent "q", TokSym SymRParen
        , TokSym SymSemi, TokSym SymRBrace
        , TokEOF
        ]

  test "qmatch with basis labels tokenizes structurally" $
    lexTokenValues "qmatch &qs { bs\"00\" => f(), bs\"01\" => g(), _ => h(), }" `shouldBe`
      Right
        [ TokKw KwQmatch, TokSym SymAmp, TokIdent "qs", TokSym SymLBrace
        , TokBasisStringLitRaw "bs\"00\"", TokSym SymFatArrow
        , TokIdent "f", TokSym SymLParen, TokSym SymRParen, TokSym SymComma
        , TokBasisStringLitRaw "bs\"01\"", TokSym SymFatArrow
        , TokIdent "g", TokSym SymLParen, TokSym SymRParen, TokSym SymComma
        , TokUnderscore, TokSym SymFatArrow
        , TokIdent "h", TokSym SymLParen, TokSym SymRParen, TokSym SymComma
        , TokSym SymRBrace
        , TokEOF
        ]

  test "qmatch with integer labels tokenizes structurally" $
    lexTokenValues "qmatch &qs { 0 => f(), 1 => g(), 2 => h(), 3 => k(), }" `shouldBe`
      Right
        [ TokKw KwQmatch, TokSym SymAmp, TokIdent "qs", TokSym SymLBrace
        , TokIntLitRaw "0", TokSym SymFatArrow
        , TokIdent "f", TokSym SymLParen, TokSym SymRParen, TokSym SymComma
        , TokIntLitRaw "1", TokSym SymFatArrow
        , TokIdent "g", TokSym SymLParen, TokSym SymRParen, TokSym SymComma
        , TokIntLitRaw "2", TokSym SymFatArrow
        , TokIdent "h", TokSym SymLParen, TokSym SymRParen, TokSym SymComma
        , TokIntLitRaw "3", TokSym SymFatArrow
        , TokIdent "k", TokSym SymLParen, TokSym SymRParen, TokSym SymComma
        , TokSym SymRBrace
        , TokEOF
        ]

  test "smatch wildcard still tokenizes lexically as underscore" $
    lexTokenValues "smatch &q { _ => one, }" `shouldBe`
      Right
        [ TokKw KwSmatch, TokSym SymAmp, TokIdent "q", TokSym SymLBrace
        , TokUnderscore, TokSym SymFatArrow, TokStateLit StateOne, TokSym SymComma
        , TokSym SymRBrace
        , TokEOF
        ]

  test "ctrl chaining with on and apply tokenizes structurally" $
    lexTokenValues "ctrl(&q0, &q1).on(bs\"10\").apply(H)(&q2)" `shouldBe`
      Right
        [ TokBuiltin BuiltinCtrl
        , TokSym SymLParen
        , TokSym SymAmp, TokIdent "q0", TokSym SymComma
        , TokSym SymAmp, TokIdent "q1"
        , TokSym SymRParen
        , TokSym SymDot, TokBuiltin BuiltinOn
        , TokSym SymLParen, TokBasisStringLitRaw "bs\"10\"", TokSym SymRParen
        , TokSym SymDot, TokBuiltin BuiltinApply
        , TokSym SymLParen, TokIdent "H", TokSym SymRParen
        , TokSym SymLParen, TokSym SymAmp, TokIdent "q2", TokSym SymRParen
        , TokEOF
        ]

  test "ctrl block form tokenizes with braces" $
    lexTokenValues "ctrl(&q0, &q1) { H(&q2); }" `shouldBe`
      Right
        [ TokBuiltin BuiltinCtrl
        , TokSym SymLParen
        , TokSym SymAmp, TokIdent "q0", TokSym SymComma
        , TokSym SymAmp, TokIdent "q1"
        , TokSym SymRParen
        , TokSym SymLBrace
        , TokIdent "H", TokSym SymLParen, TokSym SymAmp, TokIdent "q2", TokSym SymRParen
        , TokSym SymSemi
        , TokSym SymRBrace
        , TokEOF
        ]

  test "sif then selse expression tokenizes required keywords" $
    lexTokenValues "sif q then minus selse plus" `shouldBe`
      Right
        [ TokKw KwSif, TokIdent "q", TokKw KwThen
        , TokStateLit StateMinus
        , TokKw KwSelse, TokStateLit StatePlus
        , TokEOF
        ]

  test "qif qelse block expression tokenizes required keywords" $
    lexTokenValues "qif &q { X(&t); } qelse { H(&t); }" `shouldBe`
      Right
        [ TokKw KwQif, TokSym SymAmp, TokIdent "q"
        , TokSym SymLBrace
        , TokIdent "X", TokSym SymLParen, TokSym SymAmp, TokIdent "t", TokSym SymRParen, TokSym SymSemi
        , TokSym SymRBrace
        , TokKw KwQelse
        , TokSym SymLBrace
        , TokIdent "H", TokSym SymLParen, TokSym SymAmp, TokIdent "t", TokSym SymRParen, TokSym SymSemi
        , TokSym SymRBrace
        , TokEOF
        ]

  test "supports adjoint ctrl clause tokenizes keyword and builtin forms" $
    lexTokenValues "unitary fn f(q: &qbit) supports adjoint, ctrl {}" `shouldBe`
      Right
        [ TokKw KwUnitary, TokKw KwFn, TokIdent "f"
        , TokSym SymLParen
        , TokIdent "q", TokSym SymColon, TokSym SymAmp, TokTypPrim TypPrimQbit
        , TokSym SymRParen
        , TokKw KwSupports, TokKw KwAdjoint, TokSym SymComma, TokBuiltin BuiltinCtrl
        , TokSym SymLBrace, TokSym SymRBrace
        , TokEOF
        ]

  test "enum style variant paths and qenum style paths tokenize structurally" $
    lexTokenValues "Data::Left(q0) Data::Right(q1, q2)" `shouldBe`
      Right
        [ TokIdent "Data", TokSym SymDoubleColon, TokIdent "Left"
        , TokSym SymLParen, TokIdent "q0", TokSym SymRParen
        , TokIdent "Data", TokSym SymDoubleColon, TokIdent "Right"
        , TokSym SymLParen, TokIdent "q1", TokSym SymComma, TokIdent "q2", TokSym SymRParen
        , TokEOF
        ]

  ------------------------------------------------------------
  -- Symbols, paths, ranges, and member access.
  ------------------------------------------------------------
  test "reserved symbols and operators are symbol tokens" $
    let symbols =
          [ SymLParen, SymRParen, SymLBracket, SymRBracket
          , SymLBrace, SymRBrace, SymComma, SymSemi, SymColon
          , SymDoubleColon, SymDot, SymArrow, SymEq, SymWalrusEq
          , SymPlusEq, SymMinusEq, SymStarEq, SymSlashEq, SymPercentEq
          , SymPlus, SymMinus, SymStar, SymSlash, SymPercent
          , SymEqEq, SymNotEq, SymGt, SymGe, SymLt, SymLe
          , SymFatArrow, SymShr, SymShrEq, SymShl, SymShlEq
          , SymBang, SymAndAnd, SymOrOr, SymAmp, SymPipe, SymCaret
          , SymDotDot, SymDotDotEq, SymAndEq, SymOrEq, SymCaretEq
          , SymHash
          ]
     in lexTokenValues "( ) [ ] { } , ; : :: . -> = := += -= *= /= %= + - * / % == != > >= < <= => >> >>= << <<= ! && || & | ^ .. ..= &= |= ^= #" `shouldBe`
          Right (symbolTokens symbols)

  test "punctuation outside the language's reserved token set is rejected" $
    lexTokenValues "@" `shouldBe`
      Left (LexUnexpectedInput [] "@")

  test "unsupported valid Unicode is not diagnosed as malformed UTF-8" $
    let combiningAcuteAccent = "́" -- U+0301, which cannot start an identifier.
    in lexTokenValues combiningAcuteAccent `shouldBe`
      Left (LexUnexpectedOrInvalidByte 0xcc)

  test "range forms tokenize structurally" $
    lexTokenValues "a..b a..=b 1.. ..5 ..=5 .." `shouldBe`
      Right
        [ TokIdent "a", TokSym SymDotDot, TokIdent "b"
        , TokIdent "a", TokSym SymDotDotEq, TokIdent "b"
        , TokIntLitRaw "1", TokSym SymDotDot
        , TokSym SymDotDot, TokIntLitRaw "5"
        , TokSym SymDotDotEq, TokIntLitRaw "5"
        , TokSym SymDotDot
        , TokEOF
        ]

  test "paths, tuple fields, and method calls tokenize structurally" $
    lexTokenValues "my_library::helper t.0 a.len()" `shouldBe`
      Right
        [ TokIdent "my_library", TokSym SymDoubleColon, TokIdent "helper"
        , TokIdent "t", TokSym SymDot, TokIntLitRaw "0"
        , TokIdent "a", TokSym SymDot, TokIdent "len"
        , TokSym SymLParen, TokSym SymRParen
        , TokEOF
        ]

  test "top-level item forms tokenize structurally" $
    lexTokenValues "mod my_module; use my_library::helper; const I: i32 = 1;" `shouldBe`
      Right
        [ TokKw KwMod, TokIdent "my_module", TokSym SymSemi
        , TokKw KwUse, TokIdent "my_library", TokSym SymDoubleColon, TokIdent "helper", TokSym SymSemi
        , TokKw KwConst, TokIdent "I", TokSym SymColon, TokTypPrim TypPrimI32, TokSym SymEq, TokIntLitRaw "1", TokSym SymSemi
        , TokEOF
        ]

  test "if else-if else expression tokenizes structurally" $
    lexTokenValues "if x < 0 { -1 } else if x == 0 { 0 } else { 1 }" `shouldBe`
      Right
        [ TokKw KwIf, TokIdent "x", TokSym SymLt, TokIntLitRaw "0"
        , TokSym SymLBrace, TokSym SymMinus, TokIntLitRaw "1", TokSym SymRBrace
        , TokKw KwElse, TokKw KwIf, TokIdent "x", TokSym SymEqEq, TokIntLitRaw "0"
        , TokSym SymLBrace, TokIntLitRaw "0", TokSym SymRBrace
        , TokKw KwElse
        , TokSym SymLBrace, TokIntLitRaw "1", TokSym SymRBrace
        , TokEOF
        ]

  test "loop with break value tokenizes structurally" $
    lexTokenValues "loop { if count == 3 { break count; } count += 1; }" `shouldBe`
      Right
        [ TokKw KwLoop
        , TokSym SymLBrace
        , TokKw KwIf, TokIdent "count", TokSym SymEqEq, TokIntLitRaw "3"
        , TokSym SymLBrace
        , TokKw KwBreak, TokIdent "count", TokSym SymSemi
        , TokSym SymRBrace
        , TokIdent "count", TokSym SymPlusEq, TokIntLitRaw "1", TokSym SymSemi
        , TokSym SymRBrace
        , TokEOF
        ]

  test "while and for-in range loops tokenize structurally" $
    lexTokenValues "while count <= 5 { count += 1; } for i in 1..6 { f(i); }" `shouldBe`
      Right
        [ TokKw KwWhile, TokIdent "count", TokSym SymLe, TokIntLitRaw "5"
        , TokSym SymLBrace
        , TokIdent "count", TokSym SymPlusEq, TokIntLitRaw "1", TokSym SymSemi
        , TokSym SymRBrace
        , TokKw KwFor, TokIdent "i", TokKw KwIn
        , TokIntLitRaw "1", TokSym SymDotDot, TokIntLitRaw "6"
        , TokSym SymLBrace
        , TokIdent "f", TokSym SymLParen, TokIdent "i", TokSym SymRParen, TokSym SymSemi
        , TokSym SymRBrace
        , TokEOF
        ]

  test "tuple destructuring and tuple indexing tokenize structurally" $
    lexTokenValues "let (a, _, z) = (1, 2, 3); t.0 t.1 t.2" `shouldBe`
      Right
        [ TokKw KwLet
        , TokSym SymLParen, TokIdent "a", TokSym SymComma, TokUnderscore, TokSym SymComma, TokIdent "z", TokSym SymRParen
        , TokSym SymEq
        , TokSym SymLParen, TokIntLitRaw "1", TokSym SymComma, TokIntLitRaw "2", TokSym SymComma, TokIntLitRaw "3", TokSym SymRParen
        , TokSym SymSemi
        , TokIdent "t", TokSym SymDot, TokIntLitRaw "0"
        , TokIdent "t", TokSym SymDot, TokIntLitRaw "1"
        , TokIdent "t", TokSym SymDot, TokIntLitRaw "2"
        , TokEOF
        ]

  test "shared and mutable slice type forms tokenize structurally" $
    lexTokenValues "let s: &[i32] = &a[..]; let w: &mut [i32] = &mut m[1..4];" `shouldBe`
      Right
        [ TokKw KwLet, TokIdent "s", TokSym SymColon
        , TokSym SymAmp, TokSym SymLBracket, TokTypPrim TypPrimI32, TokSym SymRBracket
        , TokSym SymEq
        , TokSym SymAmp, TokIdent "a", TokSym SymLBracket, TokSym SymDotDot, TokSym SymRBracket
        , TokSym SymSemi
        , TokKw KwLet, TokIdent "w", TokSym SymColon
        , TokSym SymAmp, TokKw KwMut, TokSym SymLBracket, TokTypPrim TypPrimI32, TokSym SymRBracket
        , TokSym SymEq
        , TokSym SymAmp, TokKw KwMut, TokIdent "m", TokSym SymLBracket, TokIntLitRaw "1", TokSym SymDotDot, TokIntLitRaw "4", TokSym SymRBracket
        , TokSym SymSemi
        , TokEOF
        ]

  test "qbit slice borrow forms with ranges tokenize structurally" $
    lexTokenValues "let qv: &[qbit] = &qs[..]; let qv2: &[qbit] = &qs[..=3];" `shouldBe`
      Right
        [ TokKw KwLet, TokIdent "qv", TokSym SymColon
        , TokSym SymAmp, TokSym SymLBracket, TokTypPrim TypPrimQbit, TokSym SymRBracket
        , TokSym SymEq
        , TokSym SymAmp, TokIdent "qs", TokSym SymLBracket, TokSym SymDotDot, TokSym SymRBracket
        , TokSym SymSemi
        , TokKw KwLet, TokIdent "qv2", TokSym SymColon
        , TokSym SymAmp, TokSym SymLBracket, TokTypPrim TypPrimQbit, TokSym SymRBracket
        , TokSym SymEq
        , TokSym SymAmp, TokIdent "qs", TokSym SymLBracket, TokSym SymDotDotEq, TokIntLitRaw "3", TokSym SymRBracket
        , TokSym SymSemi
        , TokEOF
        ]

  test "slice len indexing and re-slicing tokenize with method and range separators" $
    lexTokenValues "let n = s.len(); let x = s[0]; let mid = &s[1..n-1];" `shouldBe`
      Right
        [ TokKw KwLet, TokIdent "n", TokSym SymEq
        , TokIdent "s", TokSym SymDot, TokIdent "len", TokSym SymLParen, TokSym SymRParen
        , TokSym SymSemi
        , TokKw KwLet, TokIdent "x", TokSym SymEq
        , TokIdent "s", TokSym SymLBracket, TokIntLitRaw "0", TokSym SymRBracket
        , TokSym SymSemi
        , TokKw KwLet, TokIdent "mid", TokSym SymEq
        , TokSym SymAmp, TokIdent "s", TokSym SymLBracket
        , TokIntLitRaw "1", TokSym SymDotDot, TokIdent "n", TokSym SymMinus, TokIntLitRaw "1"
        , TokSym SymRBracket
        , TokSym SymSemi
        , TokEOF
        ]

  test "recursive call form tokenizes as ordinary identifiers and delimiters" $
    lexTokenValues "sample_until_zero()" `shouldBe`
      Right [TokIdent "sample_until_zero", TokSym SymLParen, TokSym SymRParen, TokEOF]

  test "reference and walrus assignment operators tokenize structurally" $
    lexTokenValues "&x &mut x x:=5" `shouldBe`
      Right
        [ TokSym SymAmp, TokIdent "x"
        , TokSym SymAmp, TokKw KwMut, TokIdent "x"
        , TokIdent "x", TokSym SymWalrusEq, TokIntLitRaw "5"
        , TokEOF
        ]

  test "signed stabilizer terms tokenize as symbols plus identifiers" $
    lexTokenValues "+XXX -ZZ +IZZ" `shouldBe`
      Right
        [ TokSym SymPlus, TokIdent "XXX"
        , TokSym SymMinus, TokIdent "ZZ"
        , TokSym SymPlus, TokIdent "IZZ"
        , TokEOF
        ]

  test "requires and ensures clauses tokenize contract predicates" $
    lexTokenValues "requires clean(q) ensures basis(q, X)" `shouldBe`
      Right
        [ TokKw KwRequires, TokBuiltin BuiltinClean
        , TokSym SymLParen, TokIdent "q", TokSym SymRParen
        , TokKw KwEnsures, TokBuiltin BuiltinBasis
        , TokSym SymLParen, TokIdent "q", TokSym SymComma, TokIdent "X", TokSym SymRParen
        , TokEOF
        ]

  test "stabilized and product contract forms tokenize structurally" $
    lexTokenValues "ensures stabilized(qs, [+ZI, -ZZ]) ensures product([q1, q2], qs)" `shouldBe`
      Right
        [ TokKw KwEnsures, TokBuiltin BuiltinStabilized
        , TokSym SymLParen, TokIdent "qs", TokSym SymComma
        , TokSym SymLBracket
        , TokSym SymPlus, TokIdent "ZI", TokSym SymComma
        , TokSym SymMinus, TokIdent "ZZ"
        , TokSym SymRBracket, TokSym SymRParen
        , TokKw KwEnsures, TokBuiltin BuiltinProduct
        , TokSym SymLParen
        , TokSym SymLBracket, TokIdent "q1", TokSym SymComma, TokIdent "q2", TokSym SymRBracket
        , TokSym SymComma, TokIdent "qs"
        , TokSym SymRParen
        , TokEOF
        ]

  ------------------------------------------------------------
  -- Numbers.
  ------------------------------------------------------------
  test "decimal integers may contain underscores and suffixes" $
    lexTokenValues "0 1_000 123i32 123_i32 9u128 9_u128 10_u32" `shouldBe`
      Right
        [ TokIntLitRaw "0", TokIntLitRaw "1_000"
        , TokIntLitRaw "123i32", TokIntLitRaw "123_i32"
        , TokIntLitRaw "9u128", TokIntLitRaw "9_u128"
        , TokIntLitRaw "10_u32"
        , TokEOF
        ]

  test "radix integers may contain underscores and suffixes" $
    lexTokenValues "0b1010 0b_1010u8 0o7_1_i16 0xff 0xFF 0xff_u8 0x_FF_u128 0b1111_1111_1001_0000i64" `shouldBe`
      Right
        [ TokIntLitRaw "0b1010", TokIntLitRaw "0b_1010u8"
        , TokIntLitRaw "0o7_1_i16", TokIntLitRaw "0xff"
        , TokIntLitRaw "0xFF", TokIntLitRaw "0xff_u8"
        , TokIntLitRaw "0x_FF_u128"
        , TokIntLitRaw "0b1111_1111_1001_0000i64"
        , TokEOF
        ]

  test "uppercase radix prefixes are accepted" $
    lexTokenValues "0B1010 0O77 0XFF" `shouldBe`
      Right
        [ TokIntLitRaw "0B1010", TokIntLitRaw "0O77"
        , TokIntLitRaw "0XFF", TokEOF
        ]

  test "decimal floats use the supported float forms" $
    lexTokenValues "0.1 1.0 1.0e+2 1.0_f64 1e10 1E-10f32 12E+99 12E+99_f64 5f32" `shouldBe`
      Right
        [ TokFloatLitRaw "0.1"
        , TokFloatLitRaw "1.0", TokFloatLitRaw "1.0e+2"
        , TokFloatLitRaw "1.0_f64", TokFloatLitRaw "1e10"
        , TokFloatLitRaw "1E-10f32", TokFloatLitRaw "12E+99"
        , TokFloatLitRaw "12E+99_f64"
        , TokFloatLitRaw "5f32"
        , TokEOF
        ]

  test "octal integer literals with no underscore or suffix are supported" $
    lexTokenValues "0o77" `shouldBe` Right [TokIntLitRaw "0o77", TokEOF]

  test "a fractional float with a type suffix directly after the fraction (no underscore) is one literal" $
    lexTokenValues "1.0f64 0.1f32" `shouldBe`
      Right [TokFloatLitRaw "1.0f64", TokFloatLitRaw "0.1f32", TokEOF]

  test "a fractional float with a negative exponent tokenizes as one literal" $
    lexTokenValues "1.0e-3" `shouldBe` Right [TokFloatLitRaw "1.0e-3", TokEOF]

  test "invalid numeric spellings are number literal errors" $
    [ lexTokenValues "0b102"
    , lexTokenValues "0b"
    , lexTokenValues "0x"
    , lexTokenValues "0xGG"
    , lexTokenValues "1e+"
    , lexTokenValues "1.0abc"
    , lexTokenValues "5f33"
    , lexTokenValues "1e-"
    , lexTokenValues "123_i32x"
    ] `shouldBe`
      [ Left (LexInvalidNumberLiteral "0b102")
      , Left (LexInvalidNumberLiteral "0b")
      , Left (LexInvalidNumberLiteral "0x")
      , Left (LexInvalidNumberLiteral "0xGG")
      , Left (LexInvalidNumberLiteral "1e+")
      , Left (LexInvalidNumberLiteral "1.0abc")
      , Left (LexInvalidNumberLiteral "5f33")
      , Left (LexInvalidNumberLiteral "1e-")
      , Left (LexInvalidNumberLiteral "123_i32x")
      ]

  test "invalid number literal error has bounds" $
    lexErrorHasBounds "0b102" `shouldBe` Just True

  test "unary minus stays separate from integer literal" $
    lexTokenValues "-7" `shouldBe`
      Right [TokSym SymMinus, TokIntLitRaw "7", TokEOF]

  test "range does not become a trailing-dot float" $
    lexTokenValues "1..2" `shouldBe`
      Right [TokIntLitRaw "1", TokSym SymDotDot, TokIntLitRaw "2", TokEOF]

  test "digits followed by a lone dot split into an int and a dot symbol" $
    lexTokenValues "1." `shouldBe`
      Right [TokIntLitRaw "1", TokSym SymDot, TokEOF]

  test "digits followed by an inclusive range split correctly" $
    lexTokenValues "1..=2" `shouldBe`
      Right
        [ TokIntLitRaw "1", TokSym SymDotDotEq, TokIntLitRaw "2"
        , TokEOF
        ]

  test "integer and dot-operator tokens have disjoint exact bounds" $
    [ lexFile "1..2"
    , lexFile "12..=3"
    ] `shouldBe`
      [ Right
          [ B (TokIntLitRaw "1") (BS (P 0 0) (P 0 0))
          , B (TokSym SymDotDot) (BS (P 0 1) (P 0 2))
          , B (TokIntLitRaw "2") (BS (P 0 3) (P 0 3))
          , B TokEOF (BS (P 0 4) (P 0 4))
          ]
      , Right
          [ B (TokIntLitRaw "12") (BS (P 0 0) (P 0 1))
          , B (TokSym SymDotDotEq) (BS (P 0 2) (P 0 4))
          , B (TokIntLitRaw "3") (BS (P 0 5) (P 0 5))
          , B TokEOF (BS (P 0 6) (P 0 6))
          ]
      ]

  test "malformed integers before dot operators are number literal errors" $
    [ lexTokenValues "1_.x"
    , lexTokenValues "1_..2"
    , lexTokenValues "1_..=2"
    ] `shouldBe`
      [ Left (LexInvalidNumberLiteral "1_")
      , Left (LexInvalidNumberLiteral "1_")
      , Left (LexInvalidNumberLiteral "1_")
      ]

  test "malformed integer before a dot operator excludes the operator from its bounds" $
    lexFile "1_..2" `shouldBe`
      Left
        (B
          (LexInvalidNumberLiteral "1_")
          (BS (P 0 0) (P 0 1)))

  test "leading zeros are preserved in decimal integer literals" $
    lexTokenValues "007" `shouldBe` Right [TokIntLitRaw "007", TokEOF]

  test "additional malformed numeric spellings are number literal errors" $
    [ lexTokenValues "0b_"
    , lexTokenValues "1abc"
    , lexTokenValues "1u9"
    , lexTokenValues "123_"
    , lexTokenValues "1.0_"
    ] `shouldBe`
      [ Left (LexInvalidNumberLiteral "0b_")
      , Left (LexInvalidNumberLiteral "1abc")
      , Left (LexInvalidNumberLiteral "1u9")
      , Left (LexInvalidNumberLiteral "123_")
      , Left (LexInvalidNumberLiteral "1.0_")
      ]

  test "digits before dot operator still split when followed by identifiers" $
    lexTokenValues "1..x 2..=y 3.z" `shouldBe`
      Right
        [ TokIntLitRaw "1", TokSym SymDotDot, TokIdent "x"
        , TokIntLitRaw "2", TokSym SymDotDotEq, TokIdent "y"
        , TokIntLitRaw "3", TokSym SymDot, TokIdent "z"
        , TokEOF
        ]

  test "a bare inclusive range-from operator at end of input splits correctly" $
    lexTokenValues "1..=" `shouldBe`
      Right [TokIntLitRaw "1", TokSym SymDotDotEq, TokEOF]

  test "compound assignment and shift operators are recognized without surrounding whitespace" $
    lexTokenValues "x<<=1;x>>=2;x&&y;x||y;x!=y;x==y" `shouldBe`
      Right
        [ TokIdent "x", TokSym SymShlEq, TokIntLitRaw "1", TokSym SymSemi
        , TokIdent "x", TokSym SymShrEq, TokIntLitRaw "2", TokSym SymSemi
        , TokIdent "x", TokSym SymAndAnd, TokIdent "y", TokSym SymSemi
        , TokIdent "x", TokSym SymOrOr, TokIdent "y", TokSym SymSemi
        , TokIdent "x", TokSym SymNotEq, TokIdent "y", TokSym SymSemi
        , TokIdent "x", TokSym SymEqEq, TokIdent "y"
        , TokEOF
        ]

  test "slash remains an operator on both sides of comments" $
    lexTokenValues "a/b; c/=d; e/* hidden */ /f; g// hidden\r/h" `shouldBe`
      Right
        [ TokIdent "a", TokSym SymSlash, TokIdent "b", TokSym SymSemi
        , TokIdent "c", TokSym SymSlashEq, TokIdent "d", TokSym SymSemi
        , TokIdent "e", TokSym SymSlash, TokIdent "f", TokSym SymSemi
        , TokIdent "g", TokSym SymSlash, TokIdent "h"
        , TokEOF
        ]

  test "integer and float examples from the language specification retain their raw spelling" $
    lexTokenValues "1_000_000 0xff_u8 0o70_i16 0b1111_1111_1001_0000i64 12E+99_f64" `shouldBe`
      Right
        [ TokIntLitRaw "1_000_000"
        , TokIntLitRaw "0xff_u8"
        , TokIntLitRaw "0o70_i16"
        , TokIntLitRaw "0b1111_1111_1001_0000i64"
        , TokFloatLitRaw "12E+99_f64"
        , TokEOF
        ]

  ------------------------------------------------------------
  -- Strings and bytes.
  ------------------------------------------------------------
  test "normal string literals allow ASCII alphanumerics and underscore" $
    lexTokenValues "\"abc_123\"" `shouldBe`
      Right [TokStringLitRaw "\"abc_123\"", TokEOF]

  test "empty normal string literal is valid" $
    lexTokenValues "\"\"" `shouldBe` Right [TokStringLitRaw "\"\"", TokEOF]

  test "invalid normal string literals are string literal errors" $
    [ lexTokenValues "\"hello world\""
    , lexTokenValues "\"line\\nbreak\""
    ] `shouldBe`
      [ Left (LexInvalidStringLiteral "\"hello world\"")
      , Left (LexInvalidStringLiteral "\"line\\nbreak\"")
      ]

  test "closed literals containing raw tabs are invalid rather than unterminated" $
    [ lexTokenValues "\"a\tb\""
    , lexTokenValues "bs\"0\t1\""
    , lexTokenValues "b'a\t'"
    , lexTokenValues "b\"a\tb\""
    ] `shouldBe`
      [ Left (LexInvalidStringLiteral "\"a\tb\"")
      , Left (LexInvalidBasisStringLiteral "bs\"0\t1\"")
      , Left (LexInvalidByteLiteral "b'a\t'")
      , Left (LexInvalidByteStringLiteral "b\"a\tb\"")
      ]

  test "unterminated normal string is an unterminated string error" $
    lexTokenValues "\"abc" `shouldBe` Left LexUnterminatedStringLiteral

  test "a normal string literal cannot span a real line break" $
    lexTokenValues "\"abc\ndef\"" `shouldBe` Left LexUnterminatedStringLiteral

  test "a string body ending in a bare backslash at end of input is unterminated" $
    lexTokenValues "\"abc\\" `shouldBe` Left LexUnterminatedStringLiteral

  test "basis strings from multiple forms are emitted as raw basis string tokens" $
    lexTokenValues "bs\"01+-iI\" bs\"++----++\" bs\"iiiiIIIII\"" `shouldBe`
      Right
        [ TokBasisStringLitRaw "bs\"01+-iI\""
        , TokBasisStringLitRaw "bs\"++----++\""
        , TokBasisStringLitRaw "bs\"iiiiIIIII\""
        , TokEOF
        ]

  test "empty basis string literal is valid" $
    lexTokenValues "bs\"\"" `shouldBe` Right [TokBasisStringLitRaw "bs\"\"", TokEOF]

  test "invalid basis strings are basis string literal errors" $
    [ lexTokenValues "bs\"012\""
    , lexTokenValues "bs\"0 +\""
    ] `shouldBe`
      [ Left (LexInvalidBasisStringLiteral "bs\"012\"")
      , Left (LexInvalidBasisStringLiteral "bs\"0 +\"")
      ]

  test "unterminated basis string is an unterminated basis string error" $
    lexTokenValues "bs\"01" `shouldBe` Left LexUnterminatedBasisStringLiteral

  test "unterminated basis string error has bounds" $
    lexErrorHasBounds "bs\"01" `shouldBe` Just True

  test "byte literals are emitted as raw byte literal tokens" $
    lexTokenValues "b'a' b'\\n' b'\\x41'" `shouldBe`
      Right
        [ TokByteLitRaw "b'a'", TokByteLitRaw "b'\\n'"
        , TokByteLitRaw "b'\\x41'", TokEOF
        ]

  test "invalid byte literals are byte literal errors" $
    [ lexTokenValues "b'ab'"
    , lexTokenValues "b'\\q'"
    , lexTokenValues "b'\\x4G'"
    ] `shouldBe`
      [ Left (LexInvalidByteLiteral "b'ab'")
      , Left (LexInvalidByteLiteral "b'\\q'")
      , Left (LexInvalidByteLiteral "b'\\x4G'")
      ]

  test "closed byte literal with a truncated hex escape is a byte literal error" $
    lexTokenValues "b'\\x4'" `shouldBe` Left (LexInvalidByteLiteral "b'\\x4'")

  test "byte literals support every simple escape sequence" $
    lexTokenValues "b'\\r' b'\\t' b'\\0' b'\\\\' b'\\'' b'\\\"'" `shouldBe`
      Right
        [ TokByteLitRaw "b'\\r'", TokByteLitRaw "b'\\t'"
        , TokByteLitRaw "b'\\0'", TokByteLitRaw "b'\\\\'"
        , TokByteLitRaw "b'\\''", TokByteLitRaw "b'\\\"'"
        , TokEOF
        ]

  test "a byte literal ending in an escaped backslash does not swallow the next byte literal" $
    lexTokenValues "b'\\\\' b'\\''" `shouldBe`
      Right [TokByteLitRaw "b'\\\\'", TokByteLitRaw "b'\\''", TokEOF]

  test "unterminated byte literal is an unterminated byte literal error" $
    lexTokenValues "b'\\n" `shouldBe` Left LexUnterminatedByteLiteral

  test "unterminated byte literal error has bounds" $
    lexErrorHasBounds "b'\\n" `shouldBe` Just True

  test "a byte literal body ending in a bare backslash at end of input is unterminated" $
    lexTokenValues "b'\\" `shouldBe` Left LexUnterminatedByteLiteral

  test "byte strings are emitted as raw byte string tokens" $
    lexTokenValues "b\"abc\" b\"a\\n\\x41\"" `shouldBe`
      Right
        [ TokByteStringLitRaw "b\"abc\""
        , TokByteStringLitRaw "b\"a\\n\\x41\""
        , TokEOF
        ]

  test "the specification's hexadecimal byte-string example is one raw token" $
    lexTokenValues "b\"ABC\\x41\"" `shouldBe`
      Right [TokByteStringLitRaw "b\"ABC\\x41\"", TokEOF]

  test "empty byte string literal is valid" $
    lexTokenValues "b\"\"" `shouldBe` Right [TokByteStringLitRaw "b\"\"", TokEOF]

  test "byte strings support simple escapes beyond hex escapes" $
    lexTokenValues "b\"x\\ry\\tz\\0w\"" `shouldBe`
      Right [TokByteStringLitRaw "b\"x\\ry\\tz\\0w\"", TokEOF]

  test "byte strings support escaped backslash, single quote, and double quote" $
    lexTokenValues "b\"a\\\\b\\'c\\\"d\"" `shouldBe`
      Right [TokByteStringLitRaw "b\"a\\\\b\\'c\\\"d\"", TokEOF]

  test "a byte string ending in an escaped backslash does not swallow the next byte string" $
    lexTokenValues "b\"\\\\\" b\"y\"" `shouldBe`
      Right [TokByteStringLitRaw "b\"\\\\\"", TokByteStringLitRaw "b\"y\"", TokEOF]

  test "invalid byte strings are byte string literal errors" $
    [ lexTokenValues "b\"bad\\q\""
    , lexTokenValues "b\"ABC\\x4G\""
    ] `shouldBe`
      [ Left (LexInvalidByteStringLiteral "b\"bad\\q\"")
      , Left (LexInvalidByteStringLiteral "b\"ABC\\x4G\"")
      ]

  test "unterminated byte string is an unterminated byte string error" $
    lexTokenValues "b\"abc" `shouldBe` Left LexUnterminatedByteStringLiteral

  test "unterminated byte string error has bounds" $
    lexErrorHasBounds "b\"abc" `shouldBe` Just True

  test "a byte string literal cannot span a real line break" $
    lexTokenValues "b\"ab\ncd\"" `shouldBe` Left LexUnterminatedByteStringLiteral

  test "a byte string body ending in a bare backslash at end of input is unterminated" $
    lexTokenValues "b\"abc\\" `shouldBe` Left LexUnterminatedByteStringLiteral

  test "ordinary character literals request a dedicated token" $
    lexTokenValues "'a'" `shouldBe` Left LexOrdinaryCharLiteralNeedsToken

  test "multi-character ordinary literals also request a dedicated token" $
    lexTokenValues "'ab'" `shouldBe` Left LexOrdinaryCharLiteralNeedsToken

  ------------------------------------------------------------
  -- Unit literal and attributes.
  ------------------------------------------------------------
  test "unit literal lexes as punctuation" $
    lexTokenValues "()" `shouldBe`
      Right [TokSym SymLParen, TokSym SymRParen, TokEOF]

  test "attributes without arguments are tokenized structurally" $
    lexTokenValues "#[qasm_gate] #[qasm_def]" `shouldBe`
      Right
        [ TokSym SymHash, TokSym SymLBracket, TokIdent "qasm_gate"
        , TokSym SymRBracket
        , TokSym SymHash, TokSym SymLBracket, TokIdent "qasm_def"
        , TokSym SymRBracket
        , TokEOF
        ]

  test "attributes with string arguments are tokenized structurally" $
    lexTokenValues "#[qasm_gate(\"foo\")] #[qasm_def(\"qasm_subroutine_name\")]" `shouldBe`
      Right
        [ TokSym SymHash, TokSym SymLBracket, TokIdent "qasm_gate"
        , TokSym SymLParen, TokStringLitRaw "\"foo\"", TokSym SymRParen
        , TokSym SymRBracket
        , TokSym SymHash, TokSym SymLBracket, TokIdent "qasm_def"
        , TokSym SymLParen, TokStringLitRaw "\"qasm_subroutine_name\""
        , TokSym SymRParen, TokSym SymRBracket
        , TokEOF
        ]

  test "annotated unitary signature tokenizes attributes qualifiers and arrows" $
    lexTokenValues "#[qasm_gate(\"my_gate\")] unitary fn myfun(q: qbit) -> qbit { q }" `shouldBe`
      Right
        [ TokSym SymHash, TokSym SymLBracket, TokIdent "qasm_gate"
        , TokSym SymLParen, TokStringLitRaw "\"my_gate\"", TokSym SymRParen
        , TokSym SymRBracket
        , TokKw KwUnitary, TokKw KwFn, TokIdent "myfun"
        , TokSym SymLParen, TokIdent "q", TokSym SymColon, TokTypPrim TypPrimQbit, TokSym SymRParen
        , TokSym SymArrow, TokTypPrim TypPrimQbit
        , TokSym SymLBrace, TokIdent "q", TokSym SymRBrace
        , TokEOF
        ]
