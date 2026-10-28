module Frontend.Source

%default total

--------------------------------------------------------------------------------
-- Source positions and spans
--------------------------------------------------------------------------------
-- The location vocabulary shared by the lexer, parser, AST, and diagnostics.
-- A SourcePos is a point; a SourceSpan is a half-open region [start, end)
-- within one file: `end` is the position immediately AFTER the last
-- character, so two adjacent tokens share a boundary position without
-- overlapping.
--------------------------------------------------------------------------------

public export
record SourcePos where
  constructor MkSourcePos
  line   : Nat   -- 1-based
  column : Nat   -- 1-based

public export
record SourceSpan where
  constructor MkSourceSpan  -- [start, end)
  file  : String
  start : SourcePos         -- position of first character in the token
  end   : SourcePos         -- position immediately after last character

public export
record Located a where
  constructor MkLocated
  span  : SourceSpan
  value : a

public export
record SourceFileName where
  constructor MkSourceFileName
  fileName : String

--------------------------------------------------------------------------------
-- Rendering
--------------------------------------------------------------------------------

public export
showSourceSpan : SourceSpan -> String
showSourceSpan sourceSpan =
  "\{sourceSpan.file}:\{show sourceSpan.start.line}:\{show sourceSpan.start.column}"

public export
implementation Interpolation SourceSpan where
  interpolate = showSourceSpan

--------------------------------------------------------------------------------
-- Combining spans
--------------------------------------------------------------------------------
-- The span of a composite AST node is the merge of its first and last
-- constituent spans: `let q: qbit := f(q);` spans from the `let` token's
-- start to the `;` token's end.
-- Merging spans from different files and merging spans where the first span
-- starts after the second span ends is a logic error but will be detected at
-- runtime. The alternative would have been to add proofs to the type system,
-- but that would make the parser code less readable.
--------------------------------------------------------------------------------

public export
mergeSpans : SourceSpan -> SourceSpan -> SourceSpan
mergeSpans firstSpan secondSpan =
  if firstSpan.file /= secondSpan.file
     then assert_total $ idris_crash "mergeSpans: cannot merge spans from different files."
     else if positionAfter firstSpan.start secondSpan.end
             then assert_total $ idris_crash "mergeSpans: first span starts after second span ends."
             else MkSourceSpan firstSpan.file firstSpan.start secondSpan.end
  where
    positionAfter : SourcePos -> SourcePos -> Bool
    positionAfter first second =
      first.line > second.line ||
        (first.line == second.line && first.column > second.column)
