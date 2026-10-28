module Frontend.Parser.Error

import Data.List
import Text.Parse.Manual
import public Text.ParseError

import Frontend.Source

%default total

public export
data CustomParseError
    = UnsupportedFeature String
    | UnexpectedToken String
    | ParseErrorWithMessage String

public export
0 ParseError : Type
ParseError = InnerError CustomParseError

quoted : String -> String
quoted item = "'" ++ item ++ "'"

renderExpected : String -> List String -> String
renderExpected only [] = quoted only
renderExpected first [second] = quoted first ++ " or " ++ quoted second
renderExpected first (second :: rest) = quoted first ++ ", " ++ renderExpected second rest

||| The inner clause of a parse error: what went wrong
public export
renderParseError : ParseError -> String
renderParseError (Custom (UnsupportedFeature message)) = message
renderParseError (Custom (UnexpectedToken message)) = message
renderParseError (Custom (ParseErrorWithMessage message)) = message
renderParseError EOI = "unexpected end of input"
renderParseError (Expected [] actual) = "unexpected " ++ actual
renderParseError (Expected (first :: rest) actual) =
  "expected " ++ renderExpected first rest ++ ", but got " ++ actual
renderParseError (ExpectedChar charClass) = "expected " ++ interpolate charClass
renderParseError ExpectedEOI = "expected end of input"
renderParseError (InvalidControl char) = "invalid control character: " ++ show char
renderParseError InvalidEscape = "invalid escape sequence"
renderParseError (OutOfBounds value) = "value out of bounds: " ++ value
renderParseError (Unclosed value) = "unclosed " ++ value
renderParseError (Unknown value) = "unknown or invalid token: " ++ value
renderParseError (InvalidByte value) = "unexpected or invalid byte: " ++ show value

public export
implementation Show ParseError where
  show = renderParseError

public export
showParseError : Located ParseError -> String
-- `show err.value`, not `\{err.value}`: ilex-core's Text.ParseError ships 
-- interpolation with its own wording, which would silently replace ours
showParseError err = "Parse error at: \{err.span}, with message: \{show err.value}"
