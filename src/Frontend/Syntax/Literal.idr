module Frontend.Syntax.Literal

import Data.List
import Data.Maybe
import Frontend.Token
import Frontend.ASTPhases

%default total

--------------------------------------------------------------------------------
-- Literals in the AST
--------------------------------------------------------------------------------
-- One node family for every literal form in Leaf source:
--
--   1000  1_000  0xff_u8  0b1111_0000i64      -- integer literals
--   1.0  1.0e-3  12E+99_f64  5f32             -- float literals
--   "Hello"                                   -- string literals
--   b'a'  b'\n'  b'\x41'                      -- byte literals
--   b"hello"  b"ABC\x41"                      -- byte-string literals
--   bs"10+-iI"                                -- basis-string literals
--   true  false                               -- boolean literals
--   ()                                        -- unit literal
--   zero one plus minus plusi minusi          -- quantum state literals
--
--   * Numeric, string, byte, byte-string, and basis-string literals preserve
--     their RAW SOURCE SPELLING, exactly as the lexer captured it: quotes,
--     prefixes (0x/0o/0b/b/bs), digit separators (1_000), exponents, and
--     type suffixes (0xff_u8, 5f32) all included.
--------------------------------------------------------------------------------

public export
data LiteralNode
  = LiteralIntegerRaw     String          -- e.g. "1_000", "0xff_u8", "0b1010"
  | LiteralFloatRaw       String          -- e.g. "1.0e-3", "12E+99_f64", "5f32"
  | LiteralStringRaw      String          -- raw spelling including quotes
  | LiteralByteRaw        String          -- e.g. "b'a'", "b'\\x41'"
  | LiteralByteStringRaw  String          -- e.g. "b\"hello\""
  | LiteralBasisStringRaw String          -- e.g. "bs\"10+-iI\""
  | LiteralBoolean        Bool            -- true / false, already decoded
  | LiteralUnit                           -- ()
  | LiteralQuantumState   BasisStateName  -- zero / one / plus / minus / plusi / minusi

--------------------------------------------------------------------------------
-- Phase wrappers
--------------------------------------------------------------------------------

public export
Literal : AstPhase -> Type
Literal phase = AstNode phase LiteralNode

public export
SurfaceLiteral : Type
SurfaceLiteral = Literal SurfaceAstPhase

public export
CanonicalLiteral : Type
CanonicalLiteral = Literal CanonicalAstPhase

public export
ResolvedLiteral : Type
ResolvedLiteral = Literal ResolvedAstPhase

public export
TypedLiteral : Type
TypedLiteral = Literal TypedAstPhase

--------------------------------------------------------------------------------
-- Integer literal values and suffixes
--------------------------------------------------------------------------------

||| Value of a well-formed integer literal's raw spelling: digit separators, a
||| 0x/0o/0b prefix in either case and an integer type suffix are accepted,
||| e.g. "1_000", "0xff_u8", "0XFF".
public export
integerLiteralValue : String -> Maybe Nat
integerLiteralValue raw =
  let (base, rest) = splitBase (filter (/= '_') (unpack raw))
      (digits, suffix) = span (isDigitInBase base) rest
  in if null digits || not (validSuffix suffix)
       then Nothing
       else Just $ foldl (\value, digit => value * base + fromMaybe 0 (digitValue digit)) 0 digits
  where
    splitBase : List Char -> (Nat, List Char)
    splitBase literal@('0' :: baseMarker :: digits) =
      case toLower baseMarker of
        'x' => (16, digits)
        'o' => (8, digits)
        'b' => (2, digits)
        _ => (10, literal)
    splitBase digits = (10, digits)

    digitValue : Char -> Maybe Nat
    digitValue c =
      if isDigit c
        then Just (cast (ord c - ord '0'))
        else let lower = toLower c in
          if lower >= 'a' && lower <= 'f' then Just (cast (ord lower - ord 'a' + 10)) else Nothing

    isDigitInBase : Nat -> Char -> Bool
    isDigitInBase base c = maybe False (< base) (digitValue c)

    validSuffix : List Char -> Bool
    validSuffix [] = True
    validSuffix suffix = pack suffix `elem` ["i8", "i16", "i32", "i64", "i128", "u8", "u16", "u32", "u64", "u128"]

||| The integer type named by the suffix of a well-formed integer literal's raw
||| spelling, if one was written: "0xff_u8" names u8, "1_000" none. No digit
||| or base prefix contains `i` or `u`, so the suffix starts at the first one.
public export
integerLiteralSuffix : String -> Maybe TypPrimName
integerLiteralSuffix raw =
  case break (\c => c == 'i' || c == 'u') (unpack raw) of
    (_, []) => Nothing
    (_, suffix) => typeFromString (pack suffix)

||| The largest value of an unsigned integer type; Nothing for any other type.
public export
unsignedIntegerMaximum : TypPrimName -> Maybe Nat
unsignedIntegerMaximum primitiveName =
  case primitiveName of
    TypPrimU8   => Just 255
    TypPrimU16  => Just 65535
    TypPrimU32  => Just 4294967295
    TypPrimU64  => Just 18446744073709551615
    TypPrimU128 => Just 340282366920938463463374607431768211455
    _           => Nothing

||| Why a well-formed integer literal cannot be an array length. An array
||| length is unsigned, so the literal may carry only an unsigned suffix (or
||| none), and its value must fit the type that suffix names.
public export
data ArrayLengthProblem
  = SignedLengthSuffix TypPrimName                -- `3i8`
  | LengthExceedsSuffixType TypPrimName Nat       -- `256u8`, with u8's maximum

||| The problem with an integer literal's raw spelling as an array length, if any.
public export
arrayLengthProblem : String -> Maybe ArrayLengthProblem
arrayLengthProblem raw = do
  suffixType <- integerLiteralSuffix raw
  case unsignedIntegerMaximum suffixType of
    Nothing => Just (SignedLengthSuffix suffixType)
    Just maximum =>
      if maybe False (> maximum) (integerLiteralValue raw)
        then Just (LengthExceedsSuffixType suffixType maximum)
        else Nothing
