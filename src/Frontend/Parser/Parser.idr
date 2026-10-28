module Frontend.Parser.Parser

import Text.Bounds
import Text.Parse.Manual
import Text.Parse.Syntax
import Data.List1

import Frontend.ASTData
import Frontend.ASTPhases
import Frontend.Source
import Frontend.Token
import Frontend.Syntax.AST
import Frontend.Syntax.Attribute
import Frontend.Syntax.Common
import Frontend.Syntax.Contract
import Frontend.Syntax.Doc
import Frontend.Syntax.Literal
import Frontend.Syntax.Name
import Frontend.Syntax.Operator
import Frontend.Syntax.Pattern
import Frontend.Syntax.Type
import Frontend.Parser.Error
import Frontend.Parser.Helper

%default total

0 Rule : Bool -> Type -> Type
Rule strict result =
     SourceFileName
  => (nextNodeId : Nat)
  -> (tokens : List (Bounded Token))
  -> (0 acc : SuffixAcc tokens)
  -> Res strict Token tokens CustomParseError (result, Nat)

||| Transports accessibility along a parser result's suffix proof.
||| A non-consuming result retains the current witness; a consuming result uses
||| the strict-suffix recursion supplied by that witness.
0 suffixAccFrom :
     {0 strict : Bool}
  -> {0 before, after : List token}
  -> (0 suffix : Suffix strict after before)
  -> (0 acc : SuffixAcc before)
  -> SuffixAcc after
suffixAccFrom Same acc = acc
suffixAccFrom (Uncons suffix) (SA recur) = recur @{Uncons suffix}

||| Composes a parser or delimiter suffix with the current expression root.
0 suffixWithin :
     {0 strict : Bool}
  -> {0 root, before, after : List token}
  -> (0 step : Suffix strict after before)
  -> (0 within : Suffix False before root)
  -> Suffix False after root
suffixWithin step within = weaken $ trans step within

data ExpressionParseMode = CompleteExpression | StatementStartExpression

||| A recursive expression entry that is restricted to strict suffixes of
||| `root`. The mode preserves statement-leading block semantics without a
||| named back-edge from block contents to the statement dispatcher.
0 SmallerExpression : List (Bounded Token) -> Type
SmallerExpression root =
     (mode : ExpressionParseMode)
  -> (nextNodeId : Nat)
  -> (tokens : List (Bounded Token))
  -> (0 suffix : Suffix True tokens root)
  -> Res True Token tokens CustomParseError (SurfaceExpr, Nat)

||| Restricts an already-rooted expression entry to a strict suffix chosen by a type
||| parser. This lets array-length expressions share the enclosing expression's
||| structural recursion witness without calling the global expression entry.
rebaseSmaller :
     {0 root, tokens : List (Bounded Token)}
  -> SmallerExpression root
  -> (0 within : Suffix True tokens root)
  -> SmallerExpression tokens
rebaseSmaller smaller within mode nextNodeId remaining suffix =
  smaller mode nextNodeId remaining (trans suffix within)

||| A type parser whose array-length expressions are restricted to strict
||| suffixes of the type parser's current input.
0 TypeRule : Bool -> Type -> Type
TypeRule strict result =
     SourceFileName
  => (nextNodeId : Nat)
  -> (tokens : List (Bounded Token))
  -> (smaller : SmallerExpression tokens)
  -> (0 acc : SuffixAcc tokens)
  -> Res strict Token tokens CustomParseError (result, Nat)

||| A parser phase whose current input may be the root itself or any suffix of it.
0 RootedRule : Bool -> Type -> List (Bounded Token) -> Type
RootedRule strict result root =
     SourceFileName
  => (smaller : SmallerExpression root)
  -> (nextNodeId : Nat)
  -> (tokens : List (Bounded Token))
  -> (0 suffix : Suffix False tokens root)
  -> (0 acc : SuffixAcc tokens)
  -> Res strict Token tokens CustomParseError (result, Nat)

||| An expression-parser phase carrying both the recursive entry above and the
||| proof that its current input is a suffix of that entry's root input.
0 ExpressionRule : Bool -> List (Bounded Token) -> Type
ExpressionRule strict root = RootedRule strict SurfaceExpr root

||| A parser phase whose current input is known to be a strict suffix of its root.
0 NestedRule : Bool -> Type -> List (Bounded Token) -> Type
NestedRule strict result root =
     SourceFileName
  => (smaller : SmallerExpression root)
  -> (nextNodeId : Nat)
  -> (tokens : List (Bounded Token))
  -> (0 suffix : Suffix True tokens root)
  -> (0 acc : SuffixAcc tokens)
  -> Res strict Token tokens CustomParseError (result, Nat)

0 suffixWithinStrict :
     {0 strict : Bool}
  -> {0 root, before, after : List token}
  -> (0 step : Suffix strict after before)
  -> (0 within : Suffix True before root)
  -> Suffix True after root
suffixWithinStrict step within = orTrue $ trans step within

||| Parses a complete expression, including ranges and every tighter-precedence form.
||| Tested by: `fn arithmetic() {1 + 2 * 3}`.
parseExpression : Rule True SurfaceExpr

||| Parses an expression at statement position, preserving the rule that a
||| statement-leading block form ends before ordinary expression continuation.
parseStatementExpression : Rule True SurfaceExpr

||| The standard expression entry used wherever a parser hands control to the
||| expression grammar: complete expressions parse through `parseExpression`,
||| and statement-leading expressions through `parseStatementExpression`.
%inline
expressionSmaller :
     SourceFileName
  => {0 tokens : List (Bounded Token)}
  -> (0 acc : SuffixAcc tokens)
  -> SmallerExpression tokens
expressionSmaller (SA recur) CompleteExpression nextNodeId remaining suffix =
  parseExpression nextNodeId remaining (recur @{suffix})
expressionSmaller (SA recur) StatementStartExpression nextNodeId remaining suffix =
  parseStatementExpression nextNodeId remaining (recur @{suffix})

-- These declarations expose the deliberately narrow boundaries between the
-- recursive expression-parsing phases. Parsers taking `Bounds` are entered
-- with their leading keyword or builtin token already consumed; the bounds
-- are that token's source bounds.

||| Parses `ctrl(...)` controls, an optional basis clause, and the callable or
||| block continuation after the `ctrl` builtin has been consumed.
||| Tested by: `fn f() {ctrl(&q0, &q1).on(bs"10").apply(H)(&q2)}`.
parseControlExpression :
     {0 root : List (Bounded Token)}
  -> Bounds
  -> NestedRule True SurfaceExpr root

||| Parses adjoint callable syntax `(f)` or an `{ ... }` block after the
||| `adjoint` keyword has been consumed.
||| Tested by: `fn f() {adjoint(f)(q1, q2, q3)}` and
||| `fn f() {adjoint {H(&q1); CT(&q1, &q2)}}`.
parseAdjointExpression :
     {0 root : List (Bounded Token)}
  -> Bounds
  -> NestedRule True SurfaceExpr root

||| Dispatches literals, names, builtins, grouped values, collections, control
||| flow, quantum modifiers, and other primary expression forms.
||| This is where delimiter-sensitive ambiguities are resolved: `()` versus a
||| grouped expression versus a tuple, and an array literal versus
||| `[value; count]`. It creates the outer AST node before recursively parsing
||| children, so node IDs follow source-tree pre-order even when the child
||| parser is mutually recursive.
||| Tested by: `fn booleans() {true; false}`.
parsePrimaryExpression :
     {0 root : List (Bounded Token)}
  -> ExpressionRule True root

||| Repeatedly attaches calls, indexing, fields, tuple indices, and method
||| calls to an already-parsed receiver. Every recognized postfix form builds
||| a new outer expression and recursively continues, producing a maximal
||| chain such as `values()[i].field.len()`. An unrecognized token is not an
||| error: it terminates the chain and is returned untouched to the caller.
||| Tested by: `fn postfix() {values()[i].field.len()}`.
parsePostfixExpression :
     {0 root : List (Bounded Token)}
  -> SurfaceExpr
  -> ExpressionRule False root

||| Wraps a parsed braced block as an expression node.
||| Tested by: `fn block() {{1}}`.
parseBlockExpression :
     {0 root : List (Bounded Token)}
  -> ExpressionRule True root

||| Parses the body of an unconditional `loop` expression after its keyword.
||| Tested by:
||| `fn control() {loop {break}; while ready {continue}; for x in values {x}}`.
parseLoopExpression :
     {0 root : List (Bounded Token)}
  -> Bounds
  -> NestedRule True SurfaceExpr root

||| Parses a `while` condition and its braced body after the `while` keyword.
||| Tested by:
||| `fn control() {loop {break}; while ready {continue}; for x in values {x}}`.
parseWhileExpression :
     {0 root : List (Bounded Token)}
  -> Bounds
  -> NestedRule True SurfaceExpr root

||| Parses `name in expression` and a braced body after the `for` keyword.
||| Tested by:
||| `fn control() {loop {break}; while ready {continue}; for x in values {x}}`.
parseForExpression :
     {0 root : List (Bounded Token)}
  -> Bounds
  -> NestedRule True SurfaceExpr root

||| Parses the optional value of a `break` expression after its keyword.
||| Tested by: `fn exits() {break 1; continue; return; return value}`.
parseBreakExpression :
     {0 root : List (Bounded Token)}
  -> Bounds
  -> NestedRule False SurfaceExpr root

||| Builds a value-less `continue` expression after its keyword.
||| Tested by: `fn exits() {break 1; continue; return; return value}`.
parseContinueExpression :
     {0 root : List (Bounded Token)}
  -> Bounds
  -> NestedRule False SurfaceExpr root

||| Parses the optional value of a `return` expression after its keyword.
||| Tested by: `fn exits() {return; return value}`.
parseReturnExpression :
     {0 root : List (Bounded Token)}
  -> Bounds
  -> NestedRule False SurfaceExpr root

||| Parses a classical `if` after its keyword, including chained `else if` and
||| an optional `else` block.
||| Tested by: `fn choose() {if ready {1} else if retry {2} else {3}}`.
parseIfExpression :
     {0 root : List (Bounded Token)}
  -> Bounds
  -> NestedRule True SurfaceExpr root

||| Parses an identifier into a named AST node with source bounds.
||| Tested by: `fn names() {value; result}`.
parseName : String -> Rule True SurfaceName
parseName _ _ [] _ = Fail0 (B EOI NoBounds)
parseName _ nodeId ((B (TokIdent name) bounds) :: remaining) _ =
  Succ0 (makeName name bounds nodeId) remaining
parseName expectedNameDescription _ ((B token bounds) :: _) _ =
  Fail0 (B (Expected [expectedNameDescription] (describeToken token)) bounds)

||| Parses the `::name` segments following the first name of a type path.
||| The first segment is handled by `parsePathType`; this helper consumes only
||| complete `:: identifier` pairs and deliberately succeeds without consuming
||| anything when the next token is not another segment. Recursion returns the
||| merged bounds of the tail's segments (`NoBounds` is the neutral element of
||| `<+>`, so an empty tail vanishes) so the caller can span the complete path.
||| The explicit suffix composition proves that every returned token list is a
||| suffix of the original input.
||| Tested by: `fn use_types(config: my_module::Config) {}`.
parseTypePathTail : Rule False TypePathTail
parseTypePathTail nodeId
    ((B (TokSym SymDoubleColon) _) ::
     (B (TokIdent name) nameBounds) :: remaining) (SA recur) =
  let (segmentNodeId, nextNodeId) = reserveNodeId nodeId
      segment = surfaceAstNode
        (MkAstInfo segmentNodeId (sourceSpan nameBounds))
        (PathSegmentName name)
   in case succF $ parseTypePathTail nextNodeId remaining recur of
        Fail0 err => Fail0 err
        Succ0 (MkTypePathTail segments lastBounds, finalNodeId) finalTokens =>
          Succ0
            (MkTypePathTail (segment :: segments) (nameBounds <+> lastBounds),
             finalNodeId)
            finalTokens
parseTypePathTail nodeId tokens _ =
  Succ0 (MkTypePathTail [] NoBounds, nodeId) tokens @{Same}

||| Builds a named or qualified path type from its first identifier and tail.
||| Tested by: `fn use_types(person: Person, config: my_module::Config) {}`.
parsePathType :
     NodeId -> String -> Bounds -> Rule False SurfaceTy
parsePathType typeNodeId firstName firstBounds nodeId tokens acc =
  let (pathNodeId, afterPathNodeId) = reserveNodeId nodeId
      (segmentNodeId, afterSegmentNodeId) = reserveNodeId afterPathNodeId
      firstSegment = surfaceAstNode
        (MkAstInfo segmentNodeId (sourceSpan firstBounds))
        (PathSegmentName firstName)
   in case parseTypePathTail afterSegmentNodeId tokens acc of
        Fail0 err => Fail0 err
        Succ0 (MkTypePathTail segments lastBounds, finalNodeId) finalTokens =>
          let pathBounds = firstBounds <+> lastBounds
              path = surfaceAstNode
                (MkAstInfo pathNodeId (sourceSpan pathBounds))
                (MkPathNode firstSegment segments)
              ty = surfaceAstNode
                (MkAstInfo typeNodeId (sourceSpan pathBounds))
                (TyPath path)
           in Succ0 (ty, finalNodeId) finalTokens

||| Parses the `qubit` following a multiplicity qualifier. A qualifier applies to
||| a single qubit, so anything else is rejected at the token following it: a
||| second qualifier, and qubit collections, which qualify their elements.
||| Tested by: `fn qualified(q: affine qubit, pair: (linear qubit, affine qubit)) {}`.
parseQualifiedQubit :
     SourceFileName
  => NodeId
  -> SurfaceAstNode QuantumMultiplicityQualifier
  -> (nextNodeId : Nat)
  -> (tokens : List (Bounded Token))
  -> Res True Token tokens CustomParseError (SurfaceTy, Nat)
parseQualifiedQubit typeNodeId qualifier nodeId
    ((B (TokTypPrim TypPrimQubit) qubitBounds) :: remaining) =
  let (qubitNodeId, nextNodeId) = reserveNodeId nodeId
      qubitType = surfaceAstNode
        (MkAstInfo qubitNodeId (sourceSpan qubitBounds))
        (TyPrimitive TypPrimQubit)
   in Succ0
        (surfaceAstNode
          (MkAstInfo typeNodeId
            (mergeSpans qualifier.astInfo.span qubitType.astInfo.span))
          (TyQualified qualifier qubitType),
         nextNodeId)
        remaining
parseQualifiedQubit _ qualifier _ ((B token bounds) :: _) =
  failWithCustomError
    (ParseErrorWithMessage (qualifiedNonQubitMessage qualifier.value token))
    bounds
parseQualifiedQubit _ _ _ [] = Fail0 (B EOI NoBounds)

||| Wraps a parsed inner type as a reference type with the given borrow node.
wrapReferenceType :
     SourceFileName
  => {0 tokens : List (Bounded Token)}
  -> NodeId
  -> SurfaceAstNode BorrowKind
  -> Bounds
  -> Res True Token tokens CustomParseError (SurfaceTy, Nat)
  -> Res True Token tokens CustomParseError (SurfaceTy, Nat)
wrapReferenceType _ _ _ (Fail0 err) = Fail0 err
wrapReferenceType typeNodeId borrow ampBounds
    (Succ0 (inner, finalNodeId) finalTokens) =
  Succ0
    (surfaceAstNode
      (MkAstInfo typeNodeId
        (mergeSpans (sourceSpan ampBounds) inner.astInfo.span))
      (TyReference borrow inner),
     finalNodeId)
    finalTokens

mutual
  ||| Dispatches a type after its head token has already been consumed.
  ||| Indexing the result by that head makes the strict decrease visible to
  ||| the continuations parsing the rest of the type.
  parseTypeAfterHead :
       SourceFileName
    => (typeNodeId : NodeId)
    -> (nextNodeId : Nat)
    -> (token : Token)
    -> (bounds : Bounds)
    -> (remaining : List (Bounded Token))
    -> (smaller : SmallerExpression (B token bounds :: remaining))
    -> (0 acc : SuffixAcc remaining)
    -> Res True Token (B token bounds :: remaining) CustomParseError
         (SurfaceTy, Nat)
  parseTypeAfterHead typeNodeId nextNodeId token bounds remaining smaller acc =
    let afterHeadSmaller = rebaseSmaller smaller (uncons Same) in
    case token of
      TokTypPrim primitiveName =>
        Succ0
          (surfaceAstNode
            (MkAstInfo typeNodeId (sourceSpan bounds))
            (TyPrimitive primitiveName),
           nextNodeId)
          remaining
      TokSym SymLParen =>
        succT $
          parseParenType typeNodeId bounds nextNodeId remaining
            afterHeadSmaller acc
      TokSym SymLBracket =>
        succT $
          parseArrayType typeNodeId bounds nextNodeId remaining
            afterHeadSmaller acc
      TokSym SymAmp =>
        succT $
          parseReferenceType typeNodeId bounds nextNodeId remaining
            afterHeadSmaller acc
      TokIdent name =>
        succT $ parsePathType typeNodeId name bounds nextNodeId remaining acc
      TokKw keyword =>
        case storageQualifierFromKeyword keyword of
          Just storageQualifier =>
            case typeMultiplicityQualifier storageQualifier of
              Left message =>
                failWithCustomError (ParseErrorWithMessage message) bounds
              Right multiplicity =>
                let (qualifierNodeId, afterQualifierNodeId) =
                      reserveNodeId nextNodeId
                    located = surfaceAstNode
                      (MkAstInfo qualifierNodeId (sourceSpan bounds)) multiplicity
                 in succT $
                      parseQualifiedQubit typeNodeId located
                        afterQualifierNodeId remaining
          Nothing =>
            case functionEffectFromKeyword keyword of
              Just effect =>
                succT $ parseEffectFunctionType typeNodeId effect bounds
                  nextNodeId remaining
                  afterHeadSmaller acc
              Nothing =>
                case keyword of
                  KwFn =>
                    succT $ parseFunctionType typeNodeId Nothing bounds
                      nextNodeId remaining
                      afterHeadSmaller acc
                  _ =>
                    Fail0
                      (B (Expected ["a type declaration"] (describeToken token)) bounds)
      _ => Fail0 (B (Expected ["a type declaration"] (describeToken token)) bounds)

  ||| Dispatches to the parser for a primitive, path, reference, array, tuple,
  ||| qualified, or function type.
  ||| Tested by: `fn use_types(person: Person, config: my_module::Config) {}`.
  parseTypeWithin : TypeRule True SurfaceTy
  parseTypeWithin _ [] _ _ = Fail0 (B EOI NoBounds)
  parseTypeWithin nodeId ((B token bounds) :: remaining) smaller (SA recur) =
    let (typeNodeId, nextNodeId) = reserveNodeId nodeId
     in parseTypeAfterHead typeNodeId nextNodeId token bounds remaining smaller recur

  ||| Parses shared and mutable reference types beginning with `&`.
  ||| Tested by: `fn borrow(person: &Person, mutable: &mut Person) {}`.
  parseReferenceType : NodeId -> Bounds -> TypeRule True SurfaceTy
  parseReferenceType typeNodeId ampBounds nodeId
      ((B (TokKw KwMut) mutBounds) :: remaining) smaller (SA recur) =
    let (borrowNodeId, afterBorrowNodeId) = reserveNodeId nodeId
        borrow = surfaceAstNode
          (MkAstInfo borrowNodeId (sourceSpan (ampBounds <+> mutBounds)))
          MutableBorrow
     in wrapReferenceType typeNodeId borrow ampBounds $
          succT $
            parseReferentType afterBorrowNodeId remaining
              (rebaseSmaller smaller (uncons Same)) recur
  parseReferenceType typeNodeId ampBounds nodeId tokens smaller acc =
    let (borrowNodeId, afterBorrowNodeId) = reserveNodeId nodeId
        borrow = surfaceAstNode
          (MkAstInfo borrowNodeId (sourceSpan ampBounds)) SharedBorrow
     in wrapReferenceType typeNodeId borrow ampBounds $
          parseReferentType afterBorrowNodeId tokens smaller acc

  ||| Parses the type a reference refers to. A reference borrows its referent
  ||| without owning it, so a multiplicity qualifier written directly after `&`
  ||| or `&mut` is rejected here; post-parse validation rejects one nested
  ||| deeper (`&[linear qubit]`).
  ||| Tested by: `fn bad(q: &affine qubit) {}`.
  parseReferentType : TypeRule True SurfaceTy
  parseReferentType nodeId ((B token bounds) :: remaining) smaller acc =
    case multiplicityQualifierFromToken token of
      Just multiplicity =>
        failWithCustomError
          (ParseErrorWithMessage (qualifierBehindReferenceMessage multiplicity))
          bounds
      Nothing => parseTypeWithin nodeId ((B token bounds) :: remaining) smaller acc
  parseReferentType nodeId [] smaller acc = parseTypeWithin nodeId [] smaller acc

  ||| Parses an effect-qualified function type, requiring `fn` after the effect.
  ||| Tested by:
  ||| `general fn phase_kickback(oracle: unitary fn(qs: [qubit; 4], target: qubit) -> ([qubit; 4], qubit)) {}`.
  parseEffectFunctionType :
       NodeId -> FunctionEffect -> Bounds -> TypeRule True SurfaceTy
  parseEffectFunctionType typeNodeId effect effectBounds nodeId
      ((B (TokKw KwFn) fnBounds) :: remaining) smaller (SA recur) =
    let (effectNodeId, nextNodeId) = reserveNodeId nodeId
        locatedEffect = surfaceAstNode
          (MkAstInfo effectNodeId (sourceSpan effectBounds)) effect
     in succT $ parseFunctionType typeNodeId (Just locatedEffect)
          (effectBounds <+> fnBounds) nextNodeId remaining
          (rebaseSmaller smaller (uncons Same)) recur
  parseEffectFunctionType _ effect _ _ ((B token bounds) :: _) _ _ =
    Fail0 (B (Expected ["`fn` after `" ++ show effect ++ "`"] (describeToken token)) bounds)
  parseEffectFunctionType _ _ _ _ [] _ _ = Fail0 (B EOI NoBounds)

  ||| Parses one named and typed parameter inside a function type.
  ||| Tested by: `fn callback(f: fn(value: i32)) {}`.
  parseFunctionTypeParameter : TypeRule True
      (SurfaceAstNode (FunctionTypeParameterNode SurfaceAstPhase SurfaceExpr))
  parseFunctionTypeParameter nodeId tokens smaller acc@(SA recur) =
    let (parameterNodeId, afterParameterNodeId) = reserveNodeId nodeId in
    case parseName "function type parameter name" afterParameterNodeId tokens acc of
      Fail0 err => Fail0 err
      Succ0 (name, afterNameNodeId) afterName @{nameSuffix} =>
        case afterName of
          (B (TokSym SymColon) _ :: afterColon) =>
            case succT $
                   parseTypeWithin afterNameNodeId afterColon
                     (rebaseSmaller smaller (uncons nameSuffix))
                     (recur @{uncons nameSuffix}) of
              Fail0 err => Fail0 err
              Succ0 (parameterType, finalNodeId) finalTokens =>
                Succ0
                  (surfaceAstNode
                    (MkAstInfo parameterNodeId
                      (mergeSpans name.astInfo.span parameterType.astInfo.span))
                    (MkFunctionTypeParameterNode name parameterType),
                   finalNodeId)
                  finalTokens
          [] => Fail0 (B EOI NoBounds)
          (B unexpected unexpectedBounds :: _) =>
            Fail0 (B (Expected [":"] (describeToken unexpected)) unexpectedBounds)

  ||| Parses the comma-separated parameter list and closing parenthesis of a function type.
  ||| Parameters accumulate in a `SnocList` so source order is preserved without
  ||| repeatedly appending to an ordinary list. The closing `)` belongs to this
  ||| helper: it is consumed here, while its bounds are retained for the function
  ||| type's enclosing source span. A comma may introduce another parameter or be
  ||| followed immediately by `)` as a trailing comma.
  ||| Tested by: `fn callback(f: fn(value: i32)) {}`.
  parseFunctionTypeParameterList :
       SnocList (SurfaceAstNode (FunctionTypeParameterNode SurfaceAstPhase SurfaceExpr))
    -> TypeRule True
         (CommaList (SurfaceAstNode (FunctionTypeParameterNode SurfaceAstPhase SurfaceExpr)))
  parseFunctionTypeParameterList _ _ [] _ _ = Fail0 (B EOI NoBounds)
  parseFunctionTypeParameterList parsed nodeId
      ((B token tokenBounds) :: remaining) smaller acc@(SA recur) =
    if token == TokSym SymRParen
      then Succ0 (MkCommaList (parsed <>> []) tokenBounds, nodeId) remaining
      else
        case parseFunctionTypeParameter nodeId
               (B token tokenBounds :: remaining) smaller acc of
          Fail0 err => Fail0 err
          Succ0 (parameter, nextNodeId) afterParameter @{parameterSuffix} =>
            case afterParameter of
              [] => Fail0 (B EOI NoBounds)
              (B (TokSym symbol) symbolBounds) :: afterSymbol =>
                if symbol == SymRParen
                  then Succ0
                    (MkCommaList (parsed <>> [parameter]) symbolBounds, nextNodeId)
                    afterSymbol
                  else if symbol == SymComma
                    then succT $
                      parseFunctionTypeParameterList (parsed :< parameter)
                        nextNodeId afterSymbol
                        (rebaseSmaller smaller (uncons parameterSuffix))
                        (recur @{uncons parameterSuffix})
                    else
                      Fail0
                        (B (Expected [",", ")"] (describeToken (TokSym symbol)))
                           symbolBounds)
              (B unexpected unexpectedBounds) :: _ =>
                Fail0
                  (B (Expected [",", ")"] (describeToken unexpected)) unexpectedBounds)

  ||| Parses a function type, its optional effect, parameters, and optional return type.
  ||| Tested by: `fn callback(f: fn(value: i32)) {}`.
  parseFunctionType :
       NodeId
    -> Maybe (SurfaceAstNode FunctionEffect)
    -> Bounds
    -> TypeRule True SurfaceTy
  parseFunctionType _ _ _ _ [] _ _ = Fail0 (B EOI NoBounds)
  parseFunctionType typeNodeId effect startBounds nodeId
      (B (TokSym SymLParen) _ :: remaining) smaller (SA recur) =
    case succT $
           parseFunctionTypeParameterList [<] nodeId remaining
             (rebaseSmaller smaller (uncons Same)) recur of
      Fail0 err => Fail0 err
      Succ0 (MkCommaList functionParams closeBounds, afterParamsNodeId)
            afterParams @{paramsSuffix} =>
        case afterParams of
          (B (TokSym SymArrow) _ :: afterArrow) =>
            case succT $
                   parseTypeWithin afterParamsNodeId afterArrow
                     (rebaseSmaller smaller (uncons paramsSuffix))
                     (recur @{uncons paramsSuffix}) of
              Fail0 err => Fail0 err
              Succ0 (returnType, finalNodeId) finalTokens =>
                Succ0
                  (surfaceAstNode
                    (MkAstInfo typeNodeId
                      (mergeSpans (sourceSpan startBounds) returnType.astInfo.span))
                    (TyFunction effect functionParams (Just returnType)),
                   finalNodeId)
                  finalTokens
          _ =>
            Succ0
              (surfaceAstNode
                (MkAstInfo typeNodeId
                  (sourceSpan (startBounds <+> closeBounds)))
                (TyFunction effect functionParams Nothing),
               afterParamsNodeId)
              afterParams
  parseFunctionType _ _ _ _ ((B token bounds) :: _) _ _ =
    Fail0 (B (Expected ["`(` after `fn`"] (describeToken token)) bounds)

  ||| Parses slice types `[T]` and fixed-length array types `[T; expression]`.
  ||| Tested by: `fn arrays() { let b: [i32; 2 + 2]; }`.
  parseArrayType : NodeId -> Bounds -> TypeRule True SurfaceTy
  parseArrayType _ _ _ [] _ _ = Fail0 (B EOI NoBounds)
  parseArrayType arrayNodeId openBounds nodeId tokens smaller acc =
    case parseTypeWithin nodeId tokens smaller acc of
      Fail0 err => Fail0 err
      Succ0 (elementType, afterElementNodeId) afterElement @{elementSuffix} =>
        case afterElement of
          [] => Fail0 (B EOI NoBounds)
          (B (TokSym SymRBracket) closeBounds) :: finalTokens =>
            Succ0
              (surfaceAstNode
                (MkAstInfo arrayNodeId
                  (sourceSpan (openBounds <+> closeBounds)))
                (TySlice elementType),
               afterElementNodeId)
              finalTokens
          (B (TokSym SymSemi) _) :: afterSemi =>
            case succT $
                   smaller CompleteExpression afterElementNodeId afterSemi
                     (uncons elementSuffix) of
              Fail0 err => Fail0 err
              Succ0 (length, finalNodeId) afterLength =>
                case afterLength of
                  [] => Fail0 (B EOI NoBounds)
                  (B (TokSym SymRBracket) closeBounds) :: finalTokens =>
                    Succ0
                      (surfaceAstNode
                        (MkAstInfo arrayNodeId
                          (sourceSpan (openBounds <+> closeBounds)))
                        (TyArray elementType length),
                       finalNodeId)
                      finalTokens
                  (B unexpected unexpectedBounds) :: _ =>
                    Fail0 (B (Expected ["]"] (describeToken unexpected)) unexpectedBounds)
          (B unexpected unexpectedBounds) :: _ =>
            Fail0 (B (Expected ["]", ";"] (describeToken unexpected)) unexpectedBounds)

  ||| Parses unit, parenthesized, and tuple types beginning with `(`.
  ||| Tested by: `fn add(point: (i32, i32)) {}`.
  parseParenType : NodeId -> Bounds -> TypeRule True SurfaceTy
  parseParenType _ _ _ [] _ _ = Fail0 (B EOI NoBounds)
  parseParenType typeNodeId openBounds nodeId
      ((B (TokSym SymRParen) closeBounds) :: remaining) _ _ =
    Succ0 (surfaceAstNode
             (MkAstInfo typeNodeId (sourceSpan (openBounds <+> closeBounds))) TyUnit,
           nodeId) remaining
  parseParenType typeNodeId openBounds nodeId tokens smaller acc@(SA recur) =
    case parseTypeWithin nodeId tokens smaller acc of
      Fail0 err => Fail0 err
      Succ0 (firstType, afterFirstNodeId) afterFirst @{firstSuffix} =>
        case afterFirst of
          [] => Fail0 (B EOI NoBounds)
          (B (TokSym SymRParen) closeBounds) :: remaining =>
            Succ0
              (surfaceAstNode
                (MkAstInfo typeNodeId (sourceSpan (openBounds <+> closeBounds)))
                (TyParenthesized firstType),
               afterFirstNodeId)
              remaining
          (B (TokSym SymComma) _) :: afterComma =>
            case succT $
                   parseTupleTail [<] afterFirstNodeId afterComma
                     (rebaseSmaller smaller (uncons firstSuffix))
                     (recur @{uncons firstSuffix}) of
              Fail0 err => Fail0 err
              Succ0 (tail, finalNodeId) finalTokens =>
                Succ0
                  (surfaceAstNode
                    (MkAstInfo typeNodeId
                      (sourceSpan (openBounds <+> tail.closeBounds)))
                    (TyTuple (firstType ::: tail.values)),
                   finalNodeId)
                  finalTokens
          (B unexpected unexpectedBounds) :: _ =>
            Fail0 (B (Expected [",", ")"] (describeToken unexpected)) unexpectedBounds)

  ||| Parses the remaining comma-separated elements and closing `)` of a tuple type.
  ||| This helper starts after the tuple's first type and therefore also handles the
  ||| trailing-comma case. It consumes the closing delimiter and returns its bounds
  ||| separately, allowing `parseParenType` to distinguish grouping from tuple
  ||| syntax and to span the complete tuple.
  ||| Tested by: `fn qualified(pair: (linear qubit, affine qubit)) {}`.
  parseTupleTail :
       SnocList SurfaceTy
    -> TypeRule True (CommaList SurfaceTy)
  parseTupleTail _ _ [] _ _ = Fail0 (B EOI NoBounds)
  parseTupleTail parsed nodeId
      ((B token tokenBounds) :: remaining) smaller acc@(SA recur) =
    if token == TokSym SymRParen
      then Succ0 (MkCommaList (parsed <>> []) tokenBounds, nodeId) remaining
      else
        case parseTypeWithin nodeId (B token tokenBounds :: remaining) smaller acc of
          Fail0 err => Fail0 err
          Succ0 (ty, nextNodeId) afterType @{typeSuffix} =>
            case afterType of
              [] => Fail0 (B EOI NoBounds)
              (B (TokSym symbol) symbolBounds) :: afterSymbol =>
                if symbol == SymRParen
                  then Succ0
                    (MkCommaList (parsed <>> [ty]) symbolBounds, nextNodeId)
                    afterSymbol
                  else if symbol == SymComma
                    then succT $
                      parseTupleTail (parsed :< ty)
                        nextNodeId afterSymbol
                        (rebaseSmaller smaller (uncons typeSuffix))
                        (recur @{uncons typeSuffix})
                    else
                      Fail0
                        (B (Expected [",", ")"] (describeToken (TokSym symbol)))
                           symbolBounds)
              (B unexpected unexpectedBounds) :: _ =>
                Fail0
                  (B (Expected [",", ")"] (describeToken unexpected)) unexpectedBounds)

||| Ordinary type entry point. Array lengths recurse into expressions only on a
||| strict suffix of this type's input, using the current accessibility witness.
parseType : Rule True SurfaceTy
parseType nodeId tokens acc =
  parseTypeWithin nodeId tokens (expressionSmaller acc) acc

||| Detects an outer documentation comment before a parameter and reports that
||| function outer documentation comments are not supported yet. Otherwise it
||| leaves the token stream untouched and returns no comments.
||| Tested by: `fn f(\n/// docs\nx: i32) {}`.
parseParameterDocComments : Rule False (List SurfaceDocComment)
parseParameterDocComments _ ((B (TokOuterDoc _) bounds) :: _) _ =
  failWithCustomError
    (UnsupportedFeature
      "Documentation comments on function parameters are not yet supported.")
    bounds
parseParameterDocComments nodeId tokens _ =
  Succ0 ([], nodeId) tokens

||| Parses an optional `mut` modifier on a function parameter.
||| Tested by: `fn increment(mut x: i32) -> i32 { x += 1; x }`.
parseParameterMutability : Rule False (Maybe (SurfaceAstNode Mutability))
parseParameterMutability nodeId ((B (TokKw KwMut) bounds) :: remaining) _ =
  let (mutabilityNodeId, nextNodeId) = reserveNodeId nodeId
      mutability = surfaceAstNode
        (MkAstInfo mutabilityNodeId (sourceSpan bounds)) Mutable
   in Succ0 (Just mutability, nextNodeId) remaining
parseParameterMutability nodeId tokens _ =
  Succ0 (Nothing, nodeId) tokens

||| Parses one function parameter, including docs, mutability, name, and type.
||| Tested by: `fn increment(mut x: i32) -> i32 { x += 1; x }`.
parseFunctionParameter : Rule True (SurfaceFunctionParameter)
parseFunctionParameter nodeId tokens acc =
    let (parameterNodeId, nextNodeId) = reserveNodeId nodeId
        Succ0 (docs, afterDocsNodeId) afterDocs @{docsSuffix} :=
              parseParameterDocComments nextNodeId tokens acc
          | Fail0 err => Fail0 err
        Succ0 (mutability, afterMutabilityNodeId) afterMutability @{mutabilitySuffix} :=
              parseParameterMutability afterDocsNodeId afterDocs suffixAcc
          | Fail0 err => Fail0 err
        Succ0 (name, afterNameNodeId) afterName @{nameSuffix} :=
              parseName "parameter name" afterMutabilityNodeId afterMutability suffixAcc
          | Fail0 err => Fail0 err
        _ :: _ := afterName
          | [] => Fail0 (B EOI NoBounds)
        Succ0 (parameterType, finalNodeId) finalTokens @{typeSuffix} :=
              (exact (TokSym SymColon) *>
                    Text.Parse.Manual.acc (parseType afterNameNodeId)) afterName
          | Fail0 err => Fail0 err
        parameterSpan =
              mergeSpans
                (parameterStartSpan docs mutability name)
                parameterType.astInfo.span
        parameter =
              surfaceAstNode
                (MkAstInfo parameterNodeId parameterSpan)
                (NormalParameter docs mutability name parameterType)
     in Succ0 (parameter, finalNodeId) finalTokens
          @{trans typeSuffix $ trans nameSuffix $ trans mutabilitySuffix docsSuffix}

||| Parses comma-separated function parameters until the closing `)`.
||| Parsed parameters accumulate in a `SnocList`, then become an ordinary list only
||| at the delimiter. The helper consumes both commas and the closing parenthesis;
||| after a comma, parsing continues with another parameter unless the next token
||| is `)`, which accepts a trailing comma.
||| Tested by: `fn add(i: i32, point: (i32, i32)) {}`.
parseFunctionParameterList :
     SnocList (SurfaceFunctionParameter)
  -> Rule True (List (SurfaceFunctionParameter))
parseFunctionParameterList _ _ [] _ = Fail0 (B EOI NoBounds)
parseFunctionParameterList parsed nodeId
    ((B token tokenBounds) :: remaining) acc@(SA recur) =
  if token == TokSym SymRParen
    then Succ0 (parsed <>> [], nodeId) remaining
    else
      case parseFunctionParameter nodeId
             (B token tokenBounds :: remaining) acc of
        Fail0 err => Fail0 err
        Succ0 (parameter, nextNodeId) afterParameter =>
          case afterParameter of
            [] => Fail0 (B EOI NoBounds)
            (B (TokSym symbol) symbolBounds) :: afterSymbol =>
              if symbol == SymRParen
                then Succ0 (parsed <>> [parameter], nextNodeId) afterSymbol
                else if symbol == SymComma
                  then succT $
                    parseFunctionParameterList (parsed :< parameter)
                      nextNodeId afterSymbol recur
                  else
                    Fail0
                      (B (Expected [",", ")"] (describeToken (TokSym symbol)))
                         symbolBounds)
            (B unexpected unexpectedBounds) :: _ =>
              Fail0
                (B (Expected [",", ")"] (describeToken unexpected)) unexpectedBounds)

||| Parses a function declaration's parenthesized parameter list.
||| Tested by: `fn add(i: i32, point: (i32, i32)) {}`.
parseFunctionParameters : Rule True (List (SurfaceFunctionParameter))
parseFunctionParameters _ [] _ = Fail0 (B EOI NoBounds)
parseFunctionParameters nodeId tokens@(_ :: _) _ =
    (exact (TokSym SymLParen) *> acc (parseFunctionParameterList [<] nodeId)) tokens

||| Parses an optional `-> type` return annotation.
||| Tested by: `fn empty() -> () {}`.
parseOptionalReturnType : Rule False (Maybe SurfaceTy)
parseOptionalReturnType nodeId
    ((B (TokSym SymArrow) _) :: remaining) (SA recur) =
  case succF $ parseType nodeId remaining recur of
    Fail0 err => Fail0 err
    Succ0 (returnType, nextNodeId) finalTokens =>
      Succ0 (Just returnType, nextNodeId) finalTokens
parseOptionalReturnType nodeId tokens _ =
  Succ0 (Nothing, nodeId) tokens

||| Detects an optional `supports` clause and reports it as unsupported. When no
||| clause is present, it leaves the token stream untouched and returns an empty list.
||| Tested by: `fn f() supports adjoint {}`.
parseOptionalSupportClause : Rule False (List (SurfaceAstNode SupportKind))
parseOptionalSupportClause _ ((B (TokKw KwSupports) bounds) :: _) _ =
  failWithCustomError
    (UnsupportedFeature "Function `supports` clauses are not yet supported.")
    bounds
parseOptionalSupportClause nodeId tokens _ =
  Succ0 ([], nodeId) tokens

||| The shared diagnostic reported for quantum contract clauses.
unsupportedContract :
     Bounds
  -> Res False Token tokens CustomParseError (List SurfaceContractClause, Nat)
unsupportedContract bounds =
  failWithCustomError
    (UnsupportedFeature
      "Quantum contracts `requires` and/or `ensures` are not yet supported.")
    bounds

||| Detects a leading `requires` or `ensures` contract clause and reports quantum
||| contracts as unsupported. Otherwise it leaves the tokens untouched.
||| Tested by: `fn f() requires clean(q) {}` and `fn f() ensures basis(q, X) {}`.
parseContractClauses : Rule False (List SurfaceContractClause)
parseContractClauses _ ((B (TokKw KwRequires) bounds) :: _) _ =
  unsupportedContract bounds
parseContractClauses _ ((B (TokKw KwEnsures) bounds) :: _) _ =
  unsupportedContract bounds
parseContractClauses nodeId tokens _ =
  Succ0 ([], nodeId) tokens

||| Collects quantum-storage qualifiers preceding a `let` pattern.
||| Tested by: `fn allocate() {let scratch linear qs: [qubit; 2] = qalloc(2);}`.
parseLetQualifiers :
     StorageQualifiers
  -> Rule False (List (SurfaceAstNode QuantumStorageQualifier))
parseLetQualifiers qualifiers nodeId
    ((B (TokKw keyword) qualifierBounds) :: remaining) (SA recur) =
  case storageQualifierFromKeyword keyword of
    Just qualifier => consume qualifier
    Nothing => Succ0 (qualifiers.ordered <>> [], nodeId)
      (B (TokKw keyword) qualifierBounds :: remaining) @{Same}
  where
    consume :
         QuantumStorageQualifier
      -> Res False Token
           (B (TokKw keyword) qualifierBounds :: remaining)
           CustomParseError
           (List (SurfaceAstNode QuantumStorageQualifier), Nat)
    consume qualifier =
      let (qualifierNodeId, nextNodeId) = reserveNodeId nodeId
          located = surfaceAstNode
            (MkAstInfo qualifierNodeId (sourceSpan qualifierBounds)) qualifier
       in case addStorageQualifier qualifiers located of
            Left message =>
              failWithCustomError (ParseErrorWithMessage message) qualifierBounds
            Right updated =>
              succF $
                parseLetQualifiers updated nextNodeId remaining recur
parseLetQualifiers qualifiers nodeId tokens _ =
  Succ0 (qualifiers.ordered <>> [], nodeId) tokens @{Same}

mutual
  ||| Parses name, wildcard, tuple, and array patterns used by `let`.
  ||| Tested by:
  ||| `fn destructure() {let (a, b, c) = (1, 2, 3); let (x, _, z) = (1, 2, 3);}`.
  parsePattern : Rule True SurfacePattern
  parsePattern _ [] _ = Fail0 (B EOI NoBounds)
  parsePattern nodeId ((B TokUnderscore bounds) :: remaining) _ =
    let (patternNodeId, nextNodeId) = reserveNodeId nodeId
     in Succ0
          (surfaceAstNode (MkAstInfo patternNodeId (sourceSpan bounds))
            PatternWildcard,
           nextNodeId)
          remaining
  parsePattern nodeId ((B (TokIdent text) bounds) :: remaining) _ =
    let (patternNodeId, afterPatternNodeId) = reserveNodeId nodeId
        (name, nextNodeId) = makeName text bounds afterPatternNodeId
     in Succ0
          (surfaceAstNode (MkAstInfo patternNodeId (sourceSpan bounds))
            (PatternName Nothing name),
           nextNodeId)
          remaining
  parsePattern nodeId
      ((B (TokKw KwMut) mutBounds) ::
       (B (TokIdent text) nameBounds) :: remaining) _ =
    let (patternNodeId, afterPatternNodeId) = reserveNodeId nodeId
        (name, nextNodeId) = makeName text nameBounds afterPatternNodeId
     in Succ0
          (surfaceAstNode
            (MkAstInfo patternNodeId (sourceSpan (mutBounds <+> nameBounds)))
            (PatternName (Just Mutable) name),
           nextNodeId)
          remaining
  parsePattern _ ((B (TokKw KwMut) mutBounds) :: _) _ =
    failWithCustomError
      (ParseErrorWithMessage "`mut` must be followed by a binder name.")
      mutBounds
  parsePattern nodeId
      ((B (TokSym SymLParen) openBounds) ::
       (B (TokSym SymRParen) closeBounds) :: remaining) _ =
    let (patternNodeId, afterPatternNodeId) = reserveNodeId nodeId
        (literalNodeId, nextNodeId) = reserveNodeId afterPatternNodeId
        span = sourceSpan (openBounds <+> closeBounds)
        literal = surfaceAstNode (MkAstInfo literalNodeId span) LiteralUnit
     in Succ0
          (surfaceAstNode (MkAstInfo patternNodeId span)
            (PatternLiteral literal),
           nextNodeId)
          remaining
  parsePattern nodeId
      ((B (TokSym SymLParen) openBounds) :: remaining) (SA recur) =
    let (patternNodeId, afterPatternNodeId) = reserveNodeId nodeId
     in case succT $ parsePattern afterPatternNodeId remaining recur of
          Fail0 err => Fail0 err
          Succ0 (first, afterFirstNodeId) afterFirst =>
            case afterFirst of
              (B (TokSym SymRParen) closeBounds) :: finalTokens =>
                Succ0
                  (surfaceAstNode
                    (MkAstInfo patternNodeId
                      (sourceSpan (openBounds <+> closeBounds)))
                    (PatternParenthesized first),
                   afterFirstNodeId)
                  finalTokens
              (B (TokSym SymComma) _) :: afterComma =>
                case succT $
                       parseTuplePatternTail afterFirstNodeId afterComma recur of
                  Fail0 err => Fail0 err
                  Succ0 (tail, finalNodeId) finalTokens =>
                    Succ0
                      (surfaceAstNode
                        (MkAstInfo patternNodeId
                          (sourceSpan (openBounds <+> tail.closeBounds)))
                        (PatternTuple (first ::: tail.values)),
                       finalNodeId)
                      finalTokens
              (B unexpected bounds) :: _ =>
                Fail0 (B (Expected [",", ")"] (describeToken unexpected)) bounds)
              [] => Fail0 (B EOI NoBounds)
  parsePattern nodeId
      ((B (TokSym SymLBracket) openBounds) :: remaining) (SA recur) =
    let (patternNodeId, afterPatternNodeId) = reserveNodeId nodeId
     in case succT $ parseArrayPatternElements afterPatternNodeId remaining recur of
          Fail0 err => Fail0 err
          Succ0 (elements, finalNodeId) finalTokens =>
            Succ0
              (surfaceAstNode
                (MkAstInfo patternNodeId
                  (sourceSpan (openBounds <+> elements.closeBounds)))
                (PatternArray elements.values),
               finalNodeId)
              finalTokens
  parsePattern _ ((B token bounds) :: _) _ =
    Fail0 (B (Expected ["a pattern"] (describeToken token)) bounds)

  parsePatternCommaList :
       Symbol
    -> SnocList SurfacePattern
    -> Rule True (CommaList SurfacePattern)
  parsePatternCommaList _ _ _ [] _ = Fail0 (B EOI NoBounds)
  parsePatternCommaList closingSymbol parsed nodeId
      ((B token tokenBounds) :: remaining) acc@(SA recur) =
    if token == TokSym closingSymbol
      then Succ0 (MkCommaList (parsed <>> []) tokenBounds, nodeId) remaining
      else
        case parsePattern nodeId
               (B token tokenBounds :: remaining) acc of
          Fail0 err => Fail0 err
          Succ0 (pattern, nextNodeId) afterPattern =>
            case afterPattern of
              [] => Fail0 (B EOI NoBounds)
              (B (TokSym symbol) symbolBounds) :: afterSymbol =>
                if symbol == closingSymbol
                  then Succ0
                    (MkCommaList (parsed <>> [pattern]) symbolBounds, nextNodeId)
                    afterSymbol
                  else if symbol == SymComma
                    then succT $
                      parsePatternCommaList closingSymbol
                        (parsed :< pattern) nextNodeId afterSymbol recur
                    else
                      Fail0
                        (B (Expected [",", show closingSymbol]
                             (describeToken (TokSym symbol)))
                           symbolBounds)
              (B unexpected unexpectedBounds) :: _ =>
                Fail0
                  (B (Expected [",", show closingSymbol] (describeToken unexpected))
                     unexpectedBounds)

  ||| Parses the remaining elements and closing `)` of a tuple pattern.
  ||| Tested by: `fn destructure() {let (a, b, c) = (1, 2, 3);}`.
  parseTuplePatternTail : Rule True (CommaList SurfacePattern)
  parseTuplePatternTail nodeId tokens acc =
    parsePatternCommaList SymRParen [<] nodeId tokens acc

  ||| Parses the comma-separated elements and closing `]` of an array pattern.
  ||| Tested by: `fn measure() {let [b0, b1, b2]: [bit; 3] = measr(qs);}`.
  parseArrayPatternElements : Rule True (CommaList SurfacePattern)
  parseArrayPatternElements nodeId tokens acc =
    parsePatternCommaList SymRBracket [<] nodeId tokens acc

||| Parses statements and an optional trailing expression until a block's closing brace.
||| A semicolon turns an expression into `StatementSemiExpression`; an expression
||| immediately followed by `}` becomes the block's result value. Block-like
||| expressions may omit a semicolon in non-final position and are stored as
||| `StatementExpression`. Assignment operators are recognized only after parsing
||| their left expression, then delegated to `parseAssignmentStatement`.
||| Expressions are entered through the `StatementStartExpression` callback mode,
||| which prevents an unparenthesized statement-leading block form from absorbing a
||| following operator or postfix token. The closing-brace check comes first, so a
||| final block-like expression is also the block's result value; the block-like
||| check follows, before symbol/assignment dispatch, so the untouched token begins
||| the next statement.
|||
||| `blockNodeId`, the opening bounds, and accumulated statements remain stable
||| across recursion. Each recursive call advances the token suffix and threads the
||| next free node ID returned by the parser that just succeeded.
||| Tested by: `fn simple() {let i: i32 = 1;}`.
parseBlockContents :
     {0 root : List (Bounded Token)}
  -> NodeId
  -> Bounds
  -> SnocList SurfaceStatement
  -> NestedRule True SurfaceBlock root

||| Requires an opening `{` and parses a block within an existing expression
||| root, preserving the suffix evidence needed by recursively nested expressions.
parseBracedBlockWithin :
     {0 root : List (Bounded Token)}
  -> RootedRule True SurfaceBlock root

||| Requires and parses a braced block used as a function body or block-like construct.
||| Tested by: `fn empty() {}`.
parseBracedBlock : Rule True SurfaceBlock

||| Falls through to primary and postfix parsing once no unary prefix
||| operator is present. Shared by the operator dispatch below and by the
||| final catch-all clause, so the fallback is written exactly once.
||| Tested by: `fn postfix() {values()[i].field.len()}`.
parsePrimaryAndPostfix :
     {0 root : List (Bounded Token)}
  -> ExpressionRule True root
parsePrimaryAndPostfix smaller nodeId tokens suffix acc@(SA recur) =
  case parsePrimaryExpression smaller nodeId tokens suffix acc of
    Fail0 err => Fail0 err
    Succ0 (primary, afterPrimaryNodeId) afterPrimary @{primarySuffix} =>
      succT $
        parsePostfixExpression primary smaller afterPrimaryNodeId afterPrimary
          (suffixWithin primarySuffix suffix) recur

mutual
  ||| Builds a unary-operator expression node around an already-classified
  ||| operator and recurses to parse its operand. Shared by every unary
  ||| prefix form so each `parseUnaryExpression` clause only has to say which
  ||| operator it matched and how many tokens that took.
  ||| Tested by: `fn unary() {-x; !x; &x; &mut x}`.
  parseUnaryOperand :
       {0 root : List (Bounded Token)}
    -> Bounds
    -> UnaryOperator
    -> ExpressionRule True root
  parseUnaryOperand operatorBounds operatorValue smaller nodeId remaining
      suffix acc =
    let (expressionNodeId, afterExpressionNodeId) = reserveNodeId nodeId
        (operatorNodeId, afterOperatorNodeId) = reserveNodeId afterExpressionNodeId
        operator = surfaceAstNode
          (MkAstInfo operatorNodeId (sourceSpan operatorBounds)) operatorValue
     in case parseUnaryExpression smaller afterOperatorNodeId remaining suffix acc of
          Fail0 err => Fail0 err
          Succ0 (operand, finalNodeId) finalTokens =>
            Succ0
              (surfaceAstNode
                (MkAstInfo expressionNodeId
                  (mergeSpans (sourceSpan operatorBounds) operand.astInfo.span))
                (ExprUnary operator operand),
               finalNodeId)
              finalTokens

  ||| Parses prefix negation, logical not, shared borrow, mutable borrow, or a postfix expression.
  ||| `&mut` is matched here directly since it is the only two-token prefix;
  ||| every single-token prefix operator is dispatched through `unaryOperator`.
  ||| Tested by: `fn unary() {-x; !x; &x; &mut x}`.
  parseUnaryExpression :
       {0 root : List (Bounded Token)}
    -> ExpressionRule True root
  parseUnaryExpression _ _ [] _ _ = Fail0 (B EOI NoBounds)
  parseUnaryExpression smaller nodeId
      ((B (TokSym SymAmp) ampBounds) ::
       (B (TokKw KwMut) mutBounds) :: remaining) suffix (SA recur) =
    succT $
      parseUnaryOperand (ampBounds <+> mutBounds)
        (UnaryBorrow MutableBorrow) smaller nodeId remaining
        (suffixWithin (uncons $ uncons Same) suffix) recur
  parseUnaryExpression smaller nodeId
      ((B (TokSym symbol) operatorBounds) :: remaining)
      suffix (SA recur) =
    case unaryOperator symbol of
      Just operatorValue =>
        succT $
          parseUnaryOperand operatorBounds operatorValue smaller nodeId remaining
            (suffixWithin (uncons Same) suffix) recur
      Nothing =>
        parsePrimaryAndPostfix smaller nodeId
          (B (TokSym symbol) operatorBounds :: remaining) suffix (SA recur)
  parseUnaryExpression smaller nodeId tokens suffix acc =
    parsePrimaryAndPostfix smaller nodeId tokens suffix acc

||| Repeatedly attaches `as type` casts to an existing operand.
||| Tested by: `fn casts() {value as i32 as i64}`.
parseCastExpressionRest :
     {0 root : List (Bounded Token)}
  -> SurfaceExpr
  -> ExpressionRule False root
parseCastExpressionRest operand smaller nodeId
    ((B (TokKw KwAs) asBounds) :: afterAs) suffix (SA recur) =
  let (expressionNodeId, afterExpressionNodeId) = reserveNodeId nodeId
      0 typeWithin = trans (uncons Same) suffix
   in case succT $
             parseTypeWithin afterExpressionNodeId afterAs
               (rebaseSmaller smaller typeWithin) recur of
        Fail0 err => Fail0 err
        Succ0 (targetType, afterTypeNodeId) afterType @{typeSuffix} =>
          let expression = surfaceAstNode
                (MkAstInfo expressionNodeId
                  (mergeSpans operand.astInfo.span targetType.astInfo.span))
                (ExprCast operand targetType)
           in succF $
                parseCastExpressionRest expression smaller afterTypeNodeId afterType
                  (suffixWithin typeSuffix suffix) (recur @{typeSuffix})
parseCastExpressionRest operand _ nodeId tokens _ _ =
  Succ0 (operand, nodeId) tokens @{Same}

||| Parses a unary expression followed by zero or more `as type` casts.
||| Tested by: `fn casts() {x as i32; value as i32 as i64}`.
parseCastExpression :
     {0 root : List (Bounded Token)}
  -> ExpressionRule True root
parseCastExpression smaller nodeId tokens suffix acc@(SA recur) =
  case parseUnaryExpression smaller nodeId tokens suffix acc of
    Fail0 err => Fail0 err
    Succ0 (operand, afterOperandNodeId) afterOperand @{operandSuffix} =>
      succT $
        parseCastExpressionRest operand smaller afterOperandNodeId afterOperand
          (suffixWithin operandSuffix suffix) (recur @{operandSuffix})

mutual
  ||| Parses a precedence-climbing binary expression at the requested minimum precedence.
  ||| It first parses the tighter cast/unary/postfix operand, then asks
  ||| `parseBinaryExpressionRest` to extend that operand. The minimum-precedence
  ||| parameter prevents a recursive right operand from consuming an operator that
  ||| belongs to its caller.
  ||| Tested by: `fn arithmetic() {1 + 2 * 3}`.
  parseBinaryExpression :
       {0 root : List (Bounded Token)}
    -> Nat
    -> ExpressionRule True root
  parseBinaryExpression minimumPrecedence smaller nodeId tokens suffix
      acc@(SA recur) =
    case parseCastExpression smaller nodeId tokens suffix acc of
      Fail0 err => Fail0 err
      Succ0 (left, afterLeftNodeId) afterLeft @{leftSuffix} =>
        succT $
          parseBinaryExpressionRest minimumPrecedence left smaller
            afterLeftNodeId afterLeft
            (suffixWithin leftSuffix suffix) recur

  ||| Extends a parsed left operand with eligible binary operators and right operands.
  ||| For an operator with precedence `p`, the right side is parsed with minimum
  ||| precedence `p + 1`, which makes equal-precedence operators left-associative.
  ||| The combined node is then fed back into this helper at the caller's original
  ||| minimum. Unknown operators and operators below that minimum are intentionally
  ||| left unconsumed for an outer parser.
  ||| Tested by: `fn logic() {a & b ^ c | d && e || f}`.
  parseBinaryExpressionRest :
       {0 root : List (Bounded Token)}
    -> Nat
    -> SurfaceExpr
    -> ExpressionRule False root
  parseBinaryExpressionRest minimumPrecedence left smaller nodeId
      ((B (TokSym symbol) operatorBounds) :: afterOperator)
      suffix (SA recur) =
    case binaryOperator symbol of
      Nothing =>
        Succ0 (left, nodeId)
          (B (TokSym symbol) operatorBounds :: afterOperator) @{Same}
      Just (operatorValue, precedence) =>
        if precedence < minimumPrecedence
          then Succ0 (left, nodeId)
                 (B (TokSym symbol) operatorBounds :: afterOperator) @{Same}
          else if isComparisonOperator operatorValue &&
                  isUnparenthesizedComparison left
            then failWithCustomError
                   (ParseErrorWithMessage
                     "Comparison operators cannot be chained. Parenthesize one of the comparisons.")
                   operatorBounds
          else
            let (expressionNodeId, afterExpressionNodeId) = reserveNodeId nodeId
                (operatorNodeId, afterOperatorNodeId) =
                  reserveNodeId afterExpressionNodeId
                operator = surfaceAstNode
                  (MkAstInfo operatorNodeId (sourceSpan operatorBounds)) operatorValue
             in case succT $
                       parseCastExpression smaller afterOperatorNodeId afterOperator
                         (suffixWithin (uncons Same) suffix) recur of
                  Fail0 err => Fail0 err
                  Succ0 (rightOperand, afterOperandNodeId) afterOperand
                        @{operandSuffix} =>
                    case succT $
                           parseBinaryExpressionRest (S precedence) rightOperand
                             smaller afterOperandNodeId afterOperand
                             (suffixWithin operandSuffix suffix) recur of
                      Fail0 err => Fail0 err
                      Succ0 (right, afterRightNodeId) afterRight @{rightSuffix} =>
                        let expression = surfaceAstNode
                              (MkAstInfo expressionNodeId
                                (mergeSpans left.astInfo.span right.astInfo.span))
                              (ExprBinary operator left right)
                         in succF $
                              parseBinaryExpressionRest minimumPrecedence expression
                                smaller afterRightNodeId afterRight
                                (suffixWithin rightSuffix suffix) recur
  parseBinaryExpressionRest _ left _ nodeId tokens _ _ =
    Succ0 (left, nodeId) tokens @{Same}

||| Builds a range after its operator token has been consumed.
parseRangeAfterOperator :
     {0 root : List (Bounded Token)}
  -> Maybe SurfaceExpr
  -> RangeOperator
  -> Bounds
  -> NestedRule False SurfaceExpr root
parseRangeAfterOperator start rangeOperator operatorBounds
    smaller nodeId tokens suffix acc =
  let (expressionNodeId, afterExpressionNodeId) = reserveNodeId nodeId
      (operatorNodeId, afterOperatorNodeId) = reserveNodeId afterExpressionNodeId
      operatorSpan = sourceSpan operatorBounds
      operator = surfaceAstNode
        (MkAstInfo operatorNodeId operatorSpan) rangeOperator
      openEnded = case rangeOperator of
        RangeExclusive => nextTokenSatisfies isOpenRangeTerminator tokens
        RangeInclusive => False
   in if openEnded
        then
          let expressionSpan = case start of
                Just begin => mergeSpans begin.astInfo.span operatorSpan
                Nothing => operatorSpan
           in Succ0
                (surfaceAstNode
                  (MkAstInfo expressionNodeId expressionSpan)
                  (ExprRange start operator Nothing),
                 afterOperatorNodeId)
                tokens @{Same}
        else
          case parseBinaryExpression 0 smaller afterOperatorNodeId tokens
                 (weaken suffix) acc of
            Fail0 err => Fail0 err
            Succ0 (end, finalNodeId) finalTokens @{endSuffix} =>
              let expressionSpan = case start of
                    Just begin => mergeSpans begin.astInfo.span end.astInfo.span
                    Nothing => mergeSpans operatorSpan end.astInfo.span
               in Succ0
                    (surfaceAstNode
                      (MkAstInfo expressionNodeId expressionSpan)
                      (ExprRange start operator (Just end)),
                     finalNodeId)
                    finalTokens @{weaken endSuffix}

||| Parses an optional range operator and endpoint after an existing start expression.
||| The caller has already parsed the possible left endpoint. If no range operator
||| is present, it returns the original expression and token stream unchanged.
||| Tested by: `fn ranges() {1 + 2..3 * 4}`.
parseRangeExpressionRest :
     {0 root : List (Bounded Token)}
  -> SurfaceExpr
  -> ExpressionRule False root
parseRangeExpressionRest start smaller nodeId
    ((B (TokSym symbol) operatorBounds) :: remaining)
    suffix (SA recur) =
  case rangeOperator symbol of
    Just operator =>
      succF $
        parseRangeAfterOperator (Just start) operator operatorBounds
          smaller nodeId remaining (trans (uncons Same) suffix) recur
    Nothing =>
      Succ0 (start, nodeId)
        (B (TokSym symbol) operatorBounds :: remaining) @{Same}
parseRangeExpressionRest start _ nodeId tokens _ _ =
  Succ0 (start, nodeId) tokens @{Same}

||| Parses a binary expression and any range suffix following it. Shared by
||| the range-operator dispatch below and by its final catch-all clause, so
||| the fallback is written exactly once.
parseBinaryAndRange :
     {0 root : List (Bounded Token)}
  -> ExpressionRule True root
parseBinaryAndRange smaller nodeId tokens suffix acc@(SA recur) =
  case parseBinaryExpression 0 smaller nodeId tokens suffix acc of
    Fail0 err => Fail0 err
    Succ0 (start, afterStartNodeId) afterStart @{startSuffix} =>
      succT $
        parseRangeExpressionRest start smaller afterStartNodeId afterStart
          (suffixWithin startSuffix suffix) recur

||| Parses a range expression or delegates to binary-expression parsing.
||| Tested by: `fn ranges() {1..5; 1..; ..5; ..=5; ..}`.
parseRangeExpression :
     {0 root : List (Bounded Token)}
  -> ExpressionRule True root
parseRangeExpression smaller nodeId
    ((B (TokSym symbol) operatorBounds) :: remaining)
    suffix (SA recur) =
  case rangeOperator symbol of
    Just operator =>
      succT $
        parseRangeAfterOperator Nothing operator operatorBounds
          smaller nodeId remaining (trans (uncons Same) suffix) recur
    Nothing =>
      parseBinaryAndRange smaller nodeId
        (B (TokSym symbol) operatorBounds :: remaining) suffix (SA recur)
parseRangeExpression smaller nodeId tokens suffix acc =
  parseBinaryAndRange smaller nodeId tokens suffix acc

parseExpression nodeId tokens acc =
  parseRangeExpression (expressionSmaller acc) nodeId tokens Same acc

||| Continues an expression whose primary node has already been parsed.
||| Postfix operations bind first, followed by casts, binary operators, and
||| finally a possible range. Statement-position parsing uses this for callable
||| `ctrl` and `adjoint` forms only; their block forms deliberately bypass continuation.
parseExpressionContinuation :
     {0 root : List (Bounded Token)}
  -> SurfaceExpr
  -> NestedRule False SurfaceExpr root
parseExpressionContinuation primary smaller nodeId tokens suffix acc =
  let Succ0 (postfix, afterPostfixNodeId) afterPostfix @{postfixSuffix} :=
            parsePostfixExpression primary smaller nodeId tokens (weaken suffix) acc
        | Fail0 err => Fail0 err
      0 afterPostfixAcc = suffixAccFrom postfixSuffix acc
      0 afterPostfixWithin = suffixWithinStrict postfixSuffix suffix
      Succ0 (cast, afterCastNodeId) afterCast @{castSuffix} :=
            parseCastExpressionRest postfix smaller afterPostfixNodeId afterPostfix
              (weaken afterPostfixWithin) afterPostfixAcc
        | Fail0 err => Fail0 err
      0 afterCastSuffix = trans castSuffix postfixSuffix
      0 afterCastAcc = suffixAccFrom afterCastSuffix acc
      0 afterCastWithin = suffixWithinStrict castSuffix afterPostfixWithin
      Succ0 (binary, afterBinaryNodeId) afterBinary @{binarySuffix} :=
            parseBinaryExpressionRest 0 cast smaller afterCastNodeId afterCast
              (weaken afterCastWithin) afterCastAcc
        | Fail0 err => Fail0 err
      0 afterBinarySuffix = trans binarySuffix afterCastSuffix
      0 afterBinaryAcc = suffixAccFrom afterBinarySuffix acc
      0 afterBinaryWithin = suffixWithinStrict binarySuffix afterCastWithin
      Succ0 result finalTokens @{rangeSuffix} :=
            parseRangeExpressionRest binary smaller afterBinaryNodeId afterBinary
              (weaken afterBinaryWithin) afterBinaryAcc
        | Fail0 err => Fail0 err
      0 finalSuffix = trans rangeSuffix afterBinarySuffix
   in Succ0 result finalTokens
        @{finalSuffix}

||| Parses an expression at the start of a statement.
||| Unparenthesized expressions with blocks are complete statements in Leaf, so
||| this phase parses them directly and does not let the general postfix,
||| cast, binary, or range parsers consume following statement tokens.
||| Callable `ctrl` and `adjoint` forms are not block statements; after inspecting
||| their AST form, they resume through `parseExpressionContinuation`.
parseStatementExpressionWithin :
     {0 root : List (Bounded Token)}
  -> RootedRule True SurfaceExpr root
parseStatementExpressionWithin smaller nodeId
    tokens@((B (TokSym SymLBrace) _) :: _) suffix acc =
  parseBlockExpression smaller nodeId tokens suffix acc
parseStatementExpressionWithin smaller nodeId
    ((B (TokKw KwIf) bounds) :: remaining) suffix (SA recur) =
  succT $
    parseIfExpression bounds smaller nodeId remaining
      (trans (uncons Same) suffix) recur
parseStatementExpressionWithin smaller nodeId
    ((B (TokKw KwLoop) bounds) :: remaining) suffix (SA recur) =
  succT $
    parseLoopExpression bounds smaller nodeId remaining
      (trans (uncons Same) suffix) recur
parseStatementExpressionWithin smaller nodeId
    ((B (TokKw KwWhile) bounds) :: remaining) suffix (SA recur) =
  succT $
    parseWhileExpression bounds smaller nodeId remaining
      (trans (uncons Same) suffix) recur
parseStatementExpressionWithin smaller nodeId
    ((B (TokKw KwFor) bounds) :: remaining) suffix (SA recur) =
  succT $
    parseForExpression bounds smaller nodeId remaining
      (trans (uncons Same) suffix) recur
parseStatementExpressionWithin smaller nodeId
    ((B (TokBuiltin BuiltinCtrl) bounds) :: remaining) suffix (SA recur) =
  let 0 remainingWithin = trans (uncons Same) suffix in
  case parseControlExpression bounds smaller nodeId remaining remainingWithin recur of
    Fail0 err => Fail0 err
    Succ0 (control, afterControlNodeId) afterControl @{controlSuffix} =>
      let 0 resultSuffix = trans controlSuffix (uncons Same) in
      if isBlockLikeExpression control
        then Succ0 (control, afterControlNodeId) afterControl @{resultSuffix}
        else
          let 0 afterControlWithin =
                suffixWithinStrict controlSuffix remainingWithin
           in succT @{resultSuffix} $
                parseExpressionContinuation control smaller afterControlNodeId
                  afterControl afterControlWithin
                  (recur @{resultSuffix})
parseStatementExpressionWithin smaller nodeId
    ((B (TokKw KwAdjoint) bounds) :: remaining) suffix (SA recur) =
  let 0 remainingWithin = trans (uncons Same) suffix in
  case parseAdjointExpression bounds smaller nodeId remaining remainingWithin recur of
    Fail0 err => Fail0 err
    Succ0 (adjoint, afterAdjointNodeId) afterAdjoint @{adjointSuffix} =>
      let 0 resultSuffix = trans adjointSuffix (uncons Same) in
      if isBlockLikeExpression adjoint
        then Succ0 (adjoint, afterAdjointNodeId) afterAdjoint @{resultSuffix}
        else
          let 0 afterAdjointWithin =
                suffixWithinStrict adjointSuffix remainingWithin
           in succT @{resultSuffix} $
                parseExpressionContinuation adjoint smaller afterAdjointNodeId
                  afterAdjoint afterAdjointWithin
                  (recur @{resultSuffix})
parseStatementExpressionWithin smaller nodeId tokens suffix acc =
  parseRangeExpression smaller nodeId tokens suffix acc

parseStatementExpression nodeId tokens acc =
  parseStatementExpressionWithin (expressionSmaller acc) nodeId tokens Same acc

supportedLiteralFromToken : Token -> Maybe LiteralNode
supportedLiteralFromToken (TokIntLitRaw rawText) =
  Just (LiteralIntegerRaw rawText)
supportedLiteralFromToken (TokFloatLitRaw rawText) =
  Just (LiteralFloatRaw rawText)
supportedLiteralFromToken (TokBoolLit value) =
  Just (LiteralBoolean value)
supportedLiteralFromToken (TokStringLitRaw rawText) =
  Just (LiteralStringRaw rawText)
supportedLiteralFromToken (TokBasisStringLitRaw rawText) =
  Just (LiteralBasisStringRaw rawText)
supportedLiteralFromToken _ = Nothing

unsupportedPrimaryError : Token -> Maybe CustomParseError
unsupportedPrimaryError (TokKw KwQif) =
  Just (UnsupportedFeature "Quantum if expressions are not yet supported.")
unsupportedPrimaryError (TokKw KwMatch) =
  Just (UnsupportedFeature "Match expressions are not yet supported.")
unsupportedPrimaryError (TokKw KwQmatch) =
  Just (UnsupportedFeature "Quantum match expressions are not yet supported.")
unsupportedPrimaryError (TokKw KwSif) =
  Just (UnsupportedFeature "State if expressions are not yet supported.")
unsupportedPrimaryError (TokKw KwSmatch) =
  Just (UnsupportedFeature "State match expressions are not yet supported.")
unsupportedPrimaryError (TokKw KwSelf) =
  Just (UnsupportedFeature "Self expressions are not yet supported.")
unsupportedPrimaryError (TokByteLitRaw _) =
  Just (UnsupportedFeature "Byte literals are not yet supported.")
unsupportedPrimaryError (TokByteStringLitRaw _) =
  Just (UnsupportedFeature "Byte string literals are not yet supported.")
unsupportedPrimaryError (TokStateLit _) =
  Just (UnsupportedFeature "State literals are not yet supported.")
unsupportedPrimaryError _ = Nothing

||| Parses comma-separated expressions through a required closing symbol.
||| An immediate closing symbol produces an empty list; otherwise every expression
||| must be followed by a comma or the closing symbol. A trailing comma is accepted.
||| The closing bounds are returned with the values, and `smaller` restricts every
||| element to the suffix below the already-consumed opening delimiter.
||| Tested by: `fn calls() {f(); f(x, y)}`.
parseExpressionList :
     {0 root : List (Bounded Token)}
  -> Symbol
  -> SnocList SurfaceExpr
  -> (smaller : SmallerExpression root)
  -> (nextNodeId : Nat)
  -> (tokens : List (Bounded Token))
  -> (0 suffix : Suffix True tokens root)
  -> (0 acc : SuffixAcc tokens)
  -> Res True Token tokens CustomParseError
       (CommaList SurfaceExpr, Nat)
parseExpressionList _ _ _ _ [] _ _ = Fail0 (B EOI NoBounds)
parseExpressionList closingSymbol parsed smaller nodeId
    ((B token tokenBounds) :: remaining) suffix (SA recur) =
  if token == TokSym closingSymbol
    then Succ0 (MkCommaList (parsed <>> []) tokenBounds, nodeId) remaining
    else
      case smaller CompleteExpression nodeId
             (B token tokenBounds :: remaining) suffix of
        Fail0 err => Fail0 err
        Succ0 (element, nextNodeId) afterElement @{elementSuffix} =>
          case afterElement of
            [] => Fail0 (B EOI NoBounds)
            (B (TokSym symbol) symbolBounds) :: afterSymbol =>
              if symbol == closingSymbol
                then Succ0
                  (MkCommaList (parsed <>> [element]) symbolBounds, nextNodeId)
                  afterSymbol
                else if symbol == SymComma
                  then succT $
                    parseExpressionList closingSymbol
                      (parsed :< element) smaller nextNodeId
                      afterSymbol (trans (uncons elementSuffix) suffix) recur
                  else
                    Fail0
                      (B (Expected [",", show closingSymbol] (describeToken (TokSym symbol)))
                         symbolBounds)
            (B unexpected unexpectedBounds) :: _ =>
              Fail0
                (B (Expected [",", show closingSymbol] (describeToken unexpected)) unexpectedBounds)

||| Finishes a control expression as either `.apply(callable)` or a controlled block.
||| At this point the controls, and possibly `.on(basis)`, have already been parsed.
||| `.apply(...)` parses exactly one callable inside its own parentheses and builds
||| an expression that can still receive ordinary postfix calls. A leading `{`
||| instead produces the block form. Keeping these two continuations here avoids
||| treating the control-list parentheses as normal call arguments.
||| Tested by: `fn f() {ctrl(&q0, &q1) {H(&q2);}}`.
parseControlAfterControls :
     {0 root : List (Bounded Token)}
  -> NodeId
  -> Bounds
  -> List1 SurfaceExpr
  -> Maybe (SurfaceAstNode String)
  -> NestedRule True SurfaceExpr root
parseControlAfterControls _ _ _ (Just _) _ _
    ((B (TokSym SymDot) _) ::
     (B (TokBuiltin BuiltinOn) onBounds) :: _) _ _ =
  failWithCustomError
    (ParseErrorWithMessage
      "A control expression can contain only one `.on(...)` clause.")
    onBounds
parseControlAfterControls expressionNodeId ctrlBounds controls _ smaller nodeId
    ((B (TokSym SymDot) _) ::
     (B (TokBuiltin BuiltinOn) _) ::
     (B (TokSym SymLParen) _) ::
     (B (TokBasisStringLitRaw rawBasis) basisBounds) ::
     (B (TokSym SymRParen) _) :: remaining) suffix (SA recur) =
  let (basisNodeId, nextNodeId) = reserveNodeId nodeId
      basis = surfaceAstNode
        (MkAstInfo basisNodeId (sourceSpan basisBounds)) rawBasis
   in succT $
        parseControlAfterControls expressionNodeId ctrlBounds controls
          (Just basis) smaller nextNodeId remaining
          (suffixWithinStrict
            (uncons $ uncons $ uncons $ uncons $ uncons Same) suffix) recur
parseControlAfterControls expressionNodeId ctrlBounds controls onBasis smaller nodeId
    ((B (TokSym SymDot) _) ::
     (B (TokBuiltin BuiltinApply) _) ::
     (B (TokSym SymLParen) _) :: afterOpen) suffix _ =
  case succT $
         smaller CompleteExpression nodeId afterOpen
           (suffixWithinStrict (uncons $ uncons $ uncons Same) suffix) of
    Fail0 err => Fail0 err
    Succ0 (callable, afterCallableNodeId) afterCallable =>
      case afterCallable of
        (B (TokSym SymRParen) closeBounds) :: remaining =>
          Succ0
            (surfaceAstNode
              (MkAstInfo expressionNodeId
                (sourceSpan (ctrlBounds <+> closeBounds)))
              (ExprCtrl (ControlledCallable controls onBasis callable)),
             afterCallableNodeId)
            remaining
        (B unexpected unexpectedBounds) :: _ =>
          Fail0 (B (Expected [")"] (describeToken unexpected)) unexpectedBounds)
        [] => Fail0 (B EOI NoBounds)
parseControlAfterControls expressionNodeId ctrlBounds controls onBasis smaller
    nodeId tokens@((B (TokSym SymLBrace) _) :: _) suffix acc =
  case parseBracedBlockWithin smaller nodeId tokens (weaken suffix) acc of
    Fail0 err => Fail0 err
    Succ0 (body, finalNodeId) finalTokens =>
      Succ0
        (surfaceAstNode
          (MkAstInfo expressionNodeId
            (mergeSpans (sourceSpan ctrlBounds) body.astInfo.span))
          (ExprCtrl (ControlledBlock controls onBasis body)),
         finalNodeId)
        finalTokens
parseControlAfterControls _ _ _ _ _ _ [] _ _ = Fail0 (B EOI NoBounds)
parseControlAfterControls _ _ _ _ _ _
    ((B token bounds) :: _) _ _ =
  Fail0
    (B
      (Expected ["`.apply(...)` or a controlled block"] (describeToken token))
      bounds)

parseControlExpression _ _ _ [] _ _ = Fail0 (B EOI NoBounds)
parseControlExpression ctrlBounds smaller nodeId
    ((B (TokSym SymLParen) _) :: afterOpen) suffix (SA recur) =
  let (expressionNodeId, afterExpressionNodeId) = reserveNodeId nodeId
   in case succT $
             parseExpressionList SymRParen [<] smaller
               afterExpressionNodeId afterOpen
               (suffixWithinStrict (uncons Same) suffix) recur of
        Fail0 err => Fail0 err
        Succ0 (MkCommaList [] closeBounds, _) _ =>
          failWithCustomError
            (ParseErrorWithMessage
              "`ctrl` requires at least one control qubit.")
            (ctrlBounds <+> closeBounds)
        Succ0 (MkCommaList (first :: rest) closeBounds, afterControlsNodeId)
              afterControls @{controlsSuffix} =>
          succT $
            parseControlAfterControls expressionNodeId ctrlBounds
              (first ::: rest) Nothing smaller afterControlsNodeId afterControls
              (suffixWithinStrict controlsSuffix suffix) recur
parseControlExpression _ _ _ ((B token bounds) :: _) _ _ =
  Fail0 (B (Expected ["`(` after `ctrl`"] (describeToken token)) bounds)

parseAdjointExpression _ _ _ [] _ _ = Fail0 (B EOI NoBounds)
parseAdjointExpression _ _ _
    ((B (TokSym SymLParen) openBounds) ::
     (B (TokSym SymRParen) closeBounds) :: _) _ _ =
  failWithCustomError
    (ParseErrorWithMessage
      "`adjoint(...)` requires one callable expression.")
    (openBounds <+> closeBounds)
parseAdjointExpression adjointBounds smaller nodeId
    ((B (TokSym SymLParen) _) :: afterOpen) suffix _ =
  let (expressionNodeId, afterExpressionNodeId) = reserveNodeId nodeId
   in case succT $
             smaller CompleteExpression afterExpressionNodeId afterOpen
               (suffixWithinStrict (uncons Same) suffix) of
        Fail0 err => Fail0 err
        Succ0 (callable, afterCallableNodeId) afterCallable =>
          case afterCallable of
            (B (TokSym SymRParen) closeBounds) :: remaining =>
              Succ0
                (surfaceAstNode
                  (MkAstInfo expressionNodeId
                    (sourceSpan (adjointBounds <+> closeBounds)))
                  (ExprAdjoint (AdjointOfCallable callable)),
                 afterCallableNodeId)
                remaining
            (B unexpected unexpectedBounds) :: _ =>
              Fail0 (B (Expected [")"] (describeToken unexpected)) unexpectedBounds)
            [] => Fail0 (B EOI NoBounds)
parseAdjointExpression adjointBounds smaller nodeId
    ((B (TokSym SymLBrace) openBounds) :: remaining) suffix acc =
  let (expressionNodeId, afterExpressionNodeId) = reserveNodeId nodeId
   in case parseBracedBlockWithin smaller afterExpressionNodeId
               (B (TokSym SymLBrace) openBounds :: remaining) (weaken suffix) acc of
        Fail0 err => Fail0 err
        Succ0 (body, finalNodeId) finalTokens =>
          Succ0
            (surfaceAstNode
              (MkAstInfo expressionNodeId
                (mergeSpans (sourceSpan adjointBounds) body.astInfo.span))
              (ExprAdjoint (AdjointBlock body)),
             finalNodeId)
            finalTokens
parseAdjointExpression _ _ _ ((B token bounds) :: _) _ _ =
  Fail0
    (B
      (Expected ["`(` or `{` after `adjoint`"] (describeToken token))
      bounds)

||| Parses the remaining comma-separated values and closing `)` of a tuple expression.
||| Tested by: `fn tuples() {(1, true); (1, (2, 3),)}`.
parseExpressionTupleTail :
     {0 root : List (Bounded Token)}
  -> NestedRule True (CommaList SurfaceExpr) root
parseExpressionTupleTail = parseExpressionList SymRParen [<]

||| Parses unit, parenthesized, and tuple expressions after their opening `(`.
parseParenOrTupleExpression :
     {0 root : List (Bounded Token)}
  -> Bounds
  -> NestedRule True SurfaceExpr root
parseParenOrTupleExpression _ _ _ [] _ _ = Fail0 (B EOI NoBounds)
parseParenOrTupleExpression openBounds _ nodeId
    ((B (TokSym SymRParen) closeBounds) :: remaining) _ _ =
  Succ0 (makeLiteralExpression LiteralUnit (openBounds <+> closeBounds) nodeId)
    remaining
parseParenOrTupleExpression openBounds smaller nodeId tokens suffix (SA recur) =
  let (expressionNodeId, afterExpressionNodeId) = reserveNodeId nodeId
      Succ0 (first, afterFirstNodeId) afterFirst @{firstSuffix} :=
            smaller CompleteExpression afterExpressionNodeId tokens suffix
        | Fail0 err => Fail0 err
   in case afterFirst of
        (B (TokSym SymRParen) closeBounds) :: finalTokens =>
          Succ0
            (surfaceAstNode
              (MkAstInfo expressionNodeId
                (sourceSpan (openBounds <+> closeBounds)))
              (ExprParenthesized first),
             afterFirstNodeId)
            finalTokens
        (B (TokSym SymComma) _) :: afterComma =>
          let Succ0 (tail, finalNodeId) finalTokens :=
                    succT $
                      parseExpressionTupleTail smaller afterFirstNodeId afterComma
                        (suffixWithinStrict (uncons firstSuffix) suffix) recur
              | Fail0 err => Fail0 err
           in Succ0
                (surfaceAstNode
                  (MkAstInfo expressionNodeId
                    (sourceSpan (openBounds <+> tail.closeBounds)))
                  (ExprTuple (first ::: tail.values)),
                 finalNodeId)
                finalTokens
        (B unexpected unexpectedBounds) :: _ =>
          Fail0 (B (Expected [",", ")"] (describeToken unexpected)) unexpectedBounds)
        [] => Fail0 (B EOI NoBounds)

||| Parses comma-separated array elements and their closing bracket.
||| Its delimiter protocol mirrors `parseExpressionList`: an immediate `]` is an
||| empty array, commas recurse and allow a trailing comma, and the closing bounds
||| are retained for the array expression's span.
||| Tested by: `fn arrays() {[]; [1, 2, 3]; [1, 2, 3,]}`.
parseArrayElements :
     {0 root : List (Bounded Token)}
  -> NestedRule True (CommaList SurfaceExpr) root
parseArrayElements = parseExpressionList SymRBracket [<]

||| Parses array and repeated-array expressions after their opening `[`.
parseArrayExpression :
     {0 root : List (Bounded Token)}
  -> Bounds
  -> NestedRule True SurfaceExpr root
parseArrayExpression _ _ _ [] _ _ = Fail0 (B EOI NoBounds)
parseArrayExpression openBounds _ nodeId
    ((B (TokSym SymRBracket) closeBounds) :: remaining) _ _ =
  let (expressionNodeId, nextNodeId) = reserveNodeId nodeId
      expression = surfaceAstNode
        (MkAstInfo expressionNodeId (sourceSpan (openBounds <+> closeBounds)))
        (ExprArray [])
   in Succ0 (expression, nextNodeId) remaining
parseArrayExpression openBounds smaller nodeId tokens suffix (SA recur) =
  let (expressionNodeId, afterExpressionNodeId) = reserveNodeId nodeId
      Succ0 (first, afterFirstNodeId) afterFirst @{firstSuffix} :=
            smaller CompleteExpression afterExpressionNodeId tokens suffix
        | Fail0 err => Fail0 err
   in case afterFirst of
        (B (TokSym SymRBracket) closeBounds) :: finalTokens =>
          Succ0
            (surfaceAstNode
              (MkAstInfo expressionNodeId
                (sourceSpan (openBounds <+> closeBounds)))
              (ExprArray [first]),
             afterFirstNodeId)
            finalTokens
        (B (TokSym SymComma) _) :: afterComma =>
          let Succ0 (tail, finalNodeId) finalTokens :=
                    succT $
                      parseArrayElements smaller afterFirstNodeId afterComma
                        (suffixWithinStrict (uncons firstSuffix) suffix) recur
              | Fail0 err => Fail0 err
           in Succ0
                (surfaceAstNode
                  (MkAstInfo expressionNodeId
                    (sourceSpan (openBounds <+> tail.closeBounds)))
                  (ExprArray (first :: tail.values)),
                 finalNodeId)
                finalTokens
        (B (TokSym SymSemi) _) :: afterSemi =>
          let Succ0 (count, finalNodeId) afterCount :=
                    succT $
                      smaller CompleteExpression afterFirstNodeId afterSemi
                        (suffixWithinStrict (uncons firstSuffix) suffix)
              | Fail0 err => Fail0 err
              (B (TokSym SymRBracket) closeBounds) :: finalTokens := afterCount
                | (B unexpected unexpectedBounds) :: _ =>
                    Fail0 (B (Expected ["]"] (describeToken unexpected)) unexpectedBounds)
                | [] => Fail0 (B EOI NoBounds)
           in Succ0
                (surfaceAstNode
                  (MkAstInfo expressionNodeId
                    (sourceSpan (openBounds <+> closeBounds)))
                  (ExprRepeatedArray first count),
                 finalNodeId)
                finalTokens
        (B unexpected unexpectedBounds) :: _ =>
          Fail0 (B (Expected [",", ";", "]"] (describeToken unexpected)) unexpectedBounds)
        [] => Fail0 (B EOI NoBounds)

parsePrimaryExpression _ _ [] _ _ = Fail0 (B EOI NoBounds)
parsePrimaryExpression smaller nodeId
    ((B (TokSym SymLParen) openBounds) :: remaining) suffix (SA recur) =
  succT $
    parseParenOrTupleExpression openBounds smaller nodeId remaining
      (trans (uncons Same) suffix) recur
parsePrimaryExpression smaller nodeId
    ((B (TokSym SymLBracket) openBounds) :: remaining) suffix (SA recur) =
  succT $
    parseArrayExpression openBounds smaller nodeId remaining
      (trans (uncons Same) suffix) recur
parsePrimaryExpression smaller nodeId
    ((B (TokKw KwAdjoint) bounds) :: remaining) suffix (SA recur) =
  succT $
    parseAdjointExpression bounds smaller nodeId remaining
      (trans (uncons Same) suffix) recur
parsePrimaryExpression smaller nodeId
    ((B (TokBuiltin BuiltinCtrl) bounds) :: remaining) suffix (SA recur) =
  succT $
    parseControlExpression bounds smaller nodeId remaining
      (trans (uncons Same) suffix) recur
parsePrimaryExpression smaller nodeId tokens@((B (TokSym SymLBrace) _) :: _) suffix acc =
  parseBlockExpression smaller nodeId tokens suffix acc
parsePrimaryExpression smaller nodeId
    ((B (TokKw KwLoop) bounds) :: remaining) suffix (SA recur) =
  succT $
    parseLoopExpression bounds smaller nodeId remaining
      (trans (uncons Same) suffix) recur
parsePrimaryExpression smaller nodeId
    ((B (TokKw KwWhile) bounds) :: remaining) suffix (SA recur) =
  succT $
    parseWhileExpression bounds smaller nodeId remaining
      (trans (uncons Same) suffix) recur
parsePrimaryExpression smaller nodeId
    ((B (TokKw KwFor) bounds) :: remaining) suffix (SA recur) =
  succT $
    parseForExpression bounds smaller nodeId remaining
      (trans (uncons Same) suffix) recur
parsePrimaryExpression smaller nodeId
    ((B (TokKw KwBreak) bounds) :: remaining) suffix (SA recur) =
  succT $
    parseBreakExpression bounds smaller nodeId remaining
      (trans (uncons Same) suffix) recur
parsePrimaryExpression smaller nodeId
    ((B (TokKw KwContinue) bounds) :: remaining) suffix (SA recur) =
  succT $
    parseContinueExpression bounds smaller nodeId remaining
      (trans (uncons Same) suffix) recur
parsePrimaryExpression smaller nodeId
    ((B (TokKw KwReturn) bounds) :: remaining) suffix (SA recur) =
  succT $
    parseReturnExpression bounds smaller nodeId remaining
      (trans (uncons Same) suffix) recur
parsePrimaryExpression smaller nodeId
    ((B (TokKw KwIf) bounds) :: remaining) suffix (SA recur) =
  succT $
    parseIfExpression bounds smaller nodeId remaining
      (trans (uncons Same) suffix) recur
parsePrimaryExpression _ nodeId
    ((B token bounds) :: remaining) _ _ =
  case token of
    TokIdent nameText =>
      case remaining of
        (B (TokSym SymLBrace) braceBounds) :: afterBrace =>
          if startsWithUppercase nameText
            then failWithCustomError
                   (UnsupportedFeature
                     "Struct literal expressions are not yet supported.") bounds
            else Succ0 (makeNameExpression nameText bounds nodeId)
                   (B (TokSym SymLBrace) braceBounds :: afterBrace)
        (B (TokSym SymDoubleColon) _) :: _ =>
          failWithCustomError
            (UnsupportedFeature "Path expressions are not yet supported.") bounds
        _ => Succ0 (makeNameExpression nameText bounds nodeId) remaining
    TokBuiltin builtin =>
      Succ0 (makeBuiltinExpression builtin bounds nodeId) remaining
    _ =>
      case supportedLiteralFromToken token of
        Just literal =>
          Succ0 (makeLiteralExpression literal bounds nodeId) remaining
        Nothing =>
          case unsupportedPrimaryError token of
            Just err => failWithCustomError err bounds
            Nothing => Fail0 (B (Expected ["an expression"] (describeToken token)) bounds)

parsePostfixExpression callee smaller nodeId
    ((B (TokSym SymLParen) _) :: afterOpen)
    suffix (SA recur) =
  let (callNodeId, afterCallNodeId) = reserveNodeId nodeId
   in case succT $
             parseExpressionList SymRParen [<] smaller afterCallNodeId afterOpen
               (trans (uncons Same) suffix) recur of
        Fail0 err => Fail0 err
        Succ0 (arguments, afterArgumentsNodeId) afterArguments
              @{argumentsSuffix} =>
          let call = surfaceAstNode
                (MkAstInfo callNodeId
                  (mergeSpans callee.astInfo.span
                    (sourceSpan arguments.closeBounds)))
                (ExprCall callee arguments.values)
           in succF $
                parsePostfixExpression call smaller afterArgumentsNodeId
                  afterArguments (suffixWithin argumentsSuffix suffix) recur
parsePostfixExpression indexed smaller nodeId
    ((B (TokSym SymLBracket) _) :: afterOpen)
    suffix (SA recur) =
  let (indexNodeId, afterIndexNodeId) = reserveNodeId nodeId
   in case succT $
             smaller CompleteExpression afterIndexNodeId afterOpen
               (trans (uncons Same) suffix) of
        Fail0 err => Fail0 err
        Succ0 (index, afterIndexExpressionNodeId) afterIndex @{indexSuffix} =>
          case afterIndex of
            (B (TokSym SymRBracket) closeBounds) :: afterClose =>
              let expression = surfaceAstNode
                    (MkAstInfo indexNodeId
                      (mergeSpans indexed.astInfo.span (sourceSpan closeBounds)))
                    (ExprIndex indexed index)
               in succF $
                    parsePostfixExpression expression smaller
                      afterIndexExpressionNodeId afterClose
                      (suffixWithin (uncons indexSuffix) suffix) recur
            (B unexpected unexpectedBounds) :: _ =>
              Fail0 (B (Expected ["]"] (describeToken unexpected)) unexpectedBounds)
            [] => Fail0 (B EOI NoBounds)
parsePostfixExpression receiver smaller nodeId
    ((B (TokSym SymDot) _) ::
     (B (TokIdent methodText) methodBounds) ::
     (B (TokSym SymLParen) _) :: afterOpen)
    suffix (SA recur) =
  let (methodNodeId, afterMethodNodeId) = reserveNodeId nodeId
      (methodName, afterNameNodeId) = makeName methodText methodBounds afterMethodNodeId
   in case succT $
             parseExpressionList SymRParen [<] smaller afterNameNodeId afterOpen
               (trans (uncons $ uncons $ uncons Same) suffix) recur of
        Fail0 err => Fail0 err
        Succ0 (arguments, afterArgumentsNodeId) afterArguments
              @{argumentsSuffix} =>
          let expression = surfaceAstNode
                (MkAstInfo methodNodeId
                  (mergeSpans receiver.astInfo.span
                    (sourceSpan arguments.closeBounds)))
                (ExprMethodCall receiver methodName arguments.values)
           in succF $
                parsePostfixExpression expression smaller afterArgumentsNodeId
                  afterArguments (suffixWithin argumentsSuffix suffix) recur
parsePostfixExpression receiver smaller nodeId
    ((B (TokSym SymDot) _) ::
     (B (TokIdent fieldText) fieldBounds) :: afterField)
    suffix (SA recur) =
  let (fieldNodeId, afterFieldNodeId) = reserveNodeId nodeId
      (fieldName, afterNameNodeId) = makeName fieldText fieldBounds afterFieldNodeId
      expression = surfaceAstNode
        (MkAstInfo fieldNodeId
          (mergeSpans receiver.astInfo.span (sourceSpan fieldBounds)))
        (ExprField receiver fieldName)
   in succF $
        parsePostfixExpression expression smaller afterNameNodeId afterField
          (suffixWithin (uncons $ uncons Same) suffix) recur
parsePostfixExpression receiver smaller nodeId
    ((B (TokSym SymDot) _) ::
     (B (TokIntLitRaw indexRaw) indexBounds) :: afterIndex)
    suffix (SA recur) =
  let (indexNodeId, afterIndexNodeId) = reserveNodeId nodeId
      expression = surfaceAstNode
        (MkAstInfo indexNodeId
          (mergeSpans receiver.astInfo.span (sourceSpan indexBounds)))
        (ExprTupleIndex receiver indexRaw)
   in succF $
        parsePostfixExpression expression smaller afterIndexNodeId afterIndex
          (suffixWithin (uncons $ uncons Same) suffix) recur
parsePostfixExpression callee _ nodeId tokens _ _ =
  Succ0 (callee, nodeId) tokens @{Same}

parseContinueExpression continueBounds _ nodeId tokens _ _ =
  let (expressionNodeId, nextNodeId) = reserveNodeId nodeId in
  Succ0
    (surfaceAstNode
      (MkAstInfo expressionNodeId (sourceSpan continueBounds)) ExprContinue,
     nextNodeId)
    tokens

parseBlockExpression smaller nodeId tokens suffix acc =
  let (expressionNodeId, afterExpressionNodeId) = reserveNodeId nodeId
   in case parseBracedBlockWithin smaller afterExpressionNodeId tokens suffix acc of
        Fail0 err => Fail0 err
        Succ0 (block, finalNodeId) finalTokens =>
          Succ0
            (surfaceAstNode (MkAstInfo expressionNodeId block.astInfo.span)
              (ExprBlock block),
             finalNodeId)
            finalTokens

parseLoopExpression loopBounds smaller nodeId tokens suffix acc =
  let (expressionNodeId, afterExpressionNodeId) = reserveNodeId nodeId
   in case parseBracedBlockWithin smaller afterExpressionNodeId tokens
             (weaken suffix) acc of
        Fail0 err => Fail0 err
        Succ0 (body, finalNodeId) finalTokens =>
          Succ0
            (surfaceAstNode
              (MkAstInfo expressionNodeId
                (mergeSpans (sourceSpan loopBounds) body.astInfo.span))
              (ExprLoop body),
             finalNodeId)
            finalTokens

parseWhileExpression whileBounds smaller nodeId tokens suffix (SA recur) =
  let (expressionNodeId, afterExpressionNodeId) = reserveNodeId nodeId
      Succ0 (condition, afterConditionNodeId) afterCondition
            @{conditionSuffix} :=
            smaller CompleteExpression afterExpressionNodeId tokens suffix
        | Fail0 err => Fail0 err
      0 afterConditionWithin = suffixWithinStrict conditionSuffix suffix
   in case succT $
             parseBracedBlockWithin smaller afterConditionNodeId afterCondition
               (weaken afterConditionWithin) recur of
        Fail0 err => Fail0 err
        Succ0 (body, finalNodeId) finalTokens =>
          Succ0
            (surfaceAstNode
              (MkAstInfo expressionNodeId
                (mergeSpans (sourceSpan whileBounds) body.astInfo.span))
              (ExprWhile condition body),
             finalNodeId)
            finalTokens

parseForExpression _ _ _ [] _ _ = Fail0 (B EOI NoBounds)
parseForExpression forBounds smaller nodeId
    ((B (TokIdent binderText) binderBounds) ::
     (B (TokKw KwIn) _) :: remaining) suffix (SA recur) =
  let (expressionNodeId, afterExpressionNodeId) = reserveNodeId nodeId
      (patternNodeId, afterPatternNodeId) = reserveNodeId afterExpressionNodeId
      (name, afterNameNodeId) = makeName binderText binderBounds afterPatternNodeId
      pattern = surfaceAstNode (MkAstInfo patternNodeId (sourceSpan binderBounds))
                               (PatternName Nothing name)
      0 iterableWithin = suffixWithinStrict (uncons $ uncons Same) suffix
   in case succT $
             smaller CompleteExpression afterNameNodeId remaining iterableWithin of
        Fail0 err => Fail0 err
        Succ0 (iterable, afterIterableNodeId) afterIterable @{iterableSuffix} =>
          case succT $
                 parseBracedBlockWithin smaller afterIterableNodeId afterIterable
                   (weaken (suffixWithinStrict iterableSuffix suffix))
                   recur of
            Fail0 err => Fail0 err
            Succ0 (body, finalNodeId) finalTokens =>
              Succ0
                (surfaceAstNode
                  (MkAstInfo expressionNodeId
                    (mergeSpans (sourceSpan forBounds) body.astInfo.span))
                  (ExprFor pattern iterable body),
                 finalNodeId)
                finalTokens
parseForExpression forBounds _ _ _ _ _ =
  Fail0
    (B (Expected ["for identifier in expression"] (describeToken (TokKw KwFor)))
       forBounds)

||| Builds a `break` or `return` expression, parsing its optional value.
parseOptionalExitExpression :
     {0 root : List (Bounded Token)}
  -> (Maybe SurfaceExpr -> ExpressionNode SurfaceAstPhase)
  -> Bounds
  -> NestedRule False SurfaceExpr root
parseOptionalExitExpression makeExit keywordBounds smaller nodeId tokens suffix _ =
  let (expressionNodeId, afterExpressionNodeId) = reserveNodeId nodeId in
  if nextTokenSatisfies isOptionalValueTerminator tokens
    then
      Succ0
        (surfaceAstNode
          (MkAstInfo expressionNodeId (sourceSpan keywordBounds))
          (makeExit Nothing),
         afterExpressionNodeId)
        tokens @{Same}
    else
      case smaller CompleteExpression afterExpressionNodeId tokens suffix of
        Fail0 err => Fail0 err
        Succ0 (value, finalNodeId) finalTokens @{valueSuffix} =>
          Succ0
            (surfaceAstNode
              (MkAstInfo expressionNodeId
                (mergeSpans (sourceSpan keywordBounds) value.astInfo.span))
              (makeExit (Just value)),
             finalNodeId)
            finalTokens @{weaken valueSuffix}

parseBreakExpression = parseOptionalExitExpression ExprBreak

parseReturnExpression = parseOptionalExitExpression ExprReturn

parseIfExpression ifBounds smaller nodeId tokens suffix (SA recur) =
  let (expressionNodeId, afterExpressionNodeId) = reserveNodeId nodeId
      Succ0 (condition, afterConditionNodeId) afterCondition
            @{conditionSuffix} :=
            smaller CompleteExpression afterExpressionNodeId tokens suffix
        | Fail0 err => Fail0 err
      0 afterConditionWithin = suffixWithinStrict conditionSuffix suffix
      Succ0 (thenBlock, afterThenNodeId) afterThen @{thenSuffix} :=
            succT $
              parseBracedBlockWithin smaller afterConditionNodeId afterCondition
                (weaken afterConditionWithin) recur
        | Fail0 err => Fail0 err
      0 afterThenWithin = suffixWithinStrict thenSuffix suffix
      makeIfExpression : Maybe (ClassicalElseNode SurfaceAstPhase) -> SourceSpan -> SurfaceExpr
      makeIfExpression elseBranch endSpan =
        let ifSpan = mergeSpans (sourceSpan ifBounds) endSpan
            ifNode = MkClassicalIfNode condition thenBlock elseBranch
         in surfaceAstNode
              (MkAstInfo expressionNodeId ifSpan) (ExprIf ifNode)
   in case afterThen of
        (B (TokKw KwElse) _) ::
          afterElse@((B (TokSym SymLBrace) _) :: _) =>
            let 0 afterElseWithin =
                      suffixWithinStrict (uncons Same) afterThenWithin
                Succ0 (elseBlock, finalNodeId) finalTokens :=
                      succT $
                        parseBracedBlockWithin smaller afterThenNodeId afterElse
                          (weaken afterElseWithin) recur
                | Fail0 err => Fail0 err
                expression = makeIfExpression
                  (Just (ElseBlock elseBlock)) elseBlock.astInfo.span
             in Succ0 (expression, finalNodeId) finalTokens
        (B (TokKw KwElse) elseBounds) ::
          (B (TokKw KwIf) chainedIfBounds) :: afterChainedIf =>
            let 0 afterChainedWithin =
                      suffixWithinStrict (uncons $ uncons Same) afterThenWithin
                Succ0 (chainedExpression, finalNodeId) finalTokens :=
                      succT $
                        parseIfExpression chainedIfBounds smaller afterThenNodeId
                          afterChainedIf afterChainedWithin recur
                | Fail0 err => Fail0 err
             in case chainedExpression of
                  MkAstNode chainedInfo _ (ExprIf chainedIf) =>
                    let chainedNode = surfaceAstNode chainedInfo chainedIf
                        expression = makeIfExpression
                          (Just (ElseChainedIf chainedNode))
                          chainedExpression.astInfo.span
                     in Succ0 (expression, finalNodeId) finalTokens
                  _ =>
                    failWithCustomError
                      (ParseErrorWithMessage "Expected `if` after `else`.")
                      elseBounds
        _ =>
          let expression = makeIfExpression Nothing thenBlock.astInfo.span
           in Succ0 (expression, afterThenNodeId) afterThen

||| Builds a let initializer after its `=` or `:=` marker and parses the value.
||| Tested by: `fn compute() {let result := compute_value();}`.
parseLetInitializerValue :
     {0 root : List (Bounded Token)}
  -> InitializerMarker
  -> Bounds
  -> NestedRule True (LetInitializerNode SurfaceAstPhase) root
parseLetInitializerValue markerValue markerBounds smaller nodeId tokens suffix _ =
  let (markerNodeId, nextNodeId) = reserveNodeId nodeId
      marker = surfaceAstNode (MkAstInfo markerNodeId (sourceSpan markerBounds))
                              markerValue
   in case smaller CompleteExpression nextNodeId tokens suffix of
        Fail0 err => Fail0 err
        Succ0 (value, finalNodeId) finalTokens =>
          Succ0 (MkLetInitializerNode marker value, finalNodeId) finalTokens

||| Parses either an ordinary `=` or auto-uncompute `:=` let initializer.
||| Tested by: `fn compute() {let q: qubit := f(q);}`.
parseLetInitializer :
     {0 root : List (Bounded Token)}
  -> NestedRule True (LetInitializerNode SurfaceAstPhase) root
parseLetInitializer _ _ [] _ _ = Fail0 (B EOI NoBounds)
parseLetInitializer smaller nodeId
    ((B (TokSym symbol) bounds) :: remaining) suffix (SA recur) =
  case initializerMarker symbol of
    Just marker =>
      succT $
        parseLetInitializerValue marker bounds smaller nodeId remaining
          (suffixWithinStrict (uncons Same) suffix) recur
    Nothing =>
      Fail0 (B (Expected ["=", ":="] (describeToken (TokSym symbol))) bounds)
parseLetInitializer _ _ ((B token bounds) :: _) _ _ =
  Fail0 (B (Expected ["=", ":="] (describeToken token)) bounds)

||| Parses a `let` statement with qualifiers, pattern, optional type, and optional initializer.
||| The phases are deliberately ordered as they appear in source: storage qualifiers,
||| pattern, optional `: type`, then optional `=`/`:=` initializer. A semicolon is
||| always consumed by this function. At least a type or an initializer is required;
||| a typed binding may omit its initializer. Malformed punctuation after any
||| completed phase is reported at that token.
||| Tested by:
||| `fn mutable() { let mut x: i32 = 0; x = 5; let mut values = [0, 0]; values[0] = 10; }`.
parseLetStatement :
     {0 root : List (Bounded Token)}
  -> NestedRule True SurfaceStatement root
parseLetStatement _ _ [] _ _ = Fail0 (B EOI NoBounds)
parseLetStatement smaller nodeId
    ((B (TokKw KwLet) letBounds) :: remaining) suffix (SA recur) =
  let (statementNodeId, afterStatementNodeId) = reserveNodeId nodeId
      Succ0 (qualifiers, afterQualifiersNodeId) afterQualifiers
            @{qualifiersSuffix} :=
            succT $ parseLetQualifiers emptyStorageQualifiers afterStatementNodeId
              remaining recur
        | Fail0 err => Fail0 err
      Succ0 (pattern, afterPatternNodeId) afterPattern @{patternSuffix} :=
            succT $ parsePattern afterQualifiersNodeId afterQualifiers
              (recur @{qualifiersSuffix})
        | Fail0 err => Fail0 err
      makeLetStatement :
           Maybe SurfaceTy
        -> Maybe (LetInitializerNode SurfaceAstPhase)
        -> Bounds
        -> SurfaceStatement
      makeLetStatement ty initializer semiBounds =
        let binding = MkLetBindingNode qualifiers pattern ty initializer
         in surfaceAstNode
              (MkAstInfo statementNodeId
                (sourceSpan (letBounds <+> semiBounds)))
              (StatementLet binding)
   in case afterPattern of
        (B (TokSym SymColon) _) :: afterColon =>
          let 0 afterColonWithin =
                    suffixWithinStrict (uncons patternSuffix) suffix
              Succ0 (ty, afterTypeNodeId) afterType @{typeSuffix} :=
                    succT $
                      parseTypeWithin afterPatternNodeId afterColon
                        (rebaseSmaller smaller afterColonWithin)
                        (recur @{uncons patternSuffix})
                | Fail0 err => Fail0 err
           in case afterType of
                (B (TokSym SymSemi) semiBounds) :: finalTokens =>
                  Succ0
                    (makeLetStatement (Just ty) Nothing semiBounds,
                     afterTypeNodeId)
                    finalTokens
                _ =>
                  let Succ0 (initializer, finalNodeId) afterInitializer :=
                            succT $
                              parseLetInitializer smaller afterTypeNodeId afterType
                                (suffixWithinStrict typeSuffix suffix)
                                (recur @{typeSuffix})
                        | Fail0 err => Fail0 err
                      (B (TokSym SymSemi) semiBounds) :: finalTokens := afterInitializer
                        | (B unexpected bounds) :: _ =>
                            Fail0 (B (Expected [";"] (describeToken unexpected)) bounds)
                        | [] => Fail0 (B EOI NoBounds)
                   in Succ0
                        (makeLetStatement (Just ty) (Just initializer) semiBounds,
                         finalNodeId)
                        finalTokens
        (B (TokSym symbol) markerBounds) :: afterMarker =>
          case initializerMarker symbol of
            Nothing =>
              Fail0 (B (Expected [":", "=", ":="] (describeToken (TokSym symbol)))
                markerBounds)
            Just _ =>
              let Succ0 (initializer, finalNodeId) afterInitializer :=
                        succT $
                          parseLetInitializer smaller afterPatternNodeId
                            (B (TokSym symbol) markerBounds :: afterMarker)
                            (suffixWithinStrict patternSuffix suffix)
                            (recur @{patternSuffix})
                  | Fail0 err => Fail0 err
                  (B (TokSym SymSemi) semiBounds) :: finalTokens := afterInitializer
                    | (B unexpected bounds) :: _ =>
                        Fail0 (B (Expected [";"] (describeToken unexpected)) bounds)
                    | [] => Fail0 (B EOI NoBounds)
               in Succ0
                    (makeLetStatement Nothing (Just initializer) semiBounds,
                     finalNodeId)
                    finalTokens
        (B unexpected bounds) :: _ =>
          Fail0 (B (Expected [":", "=", ":="] (describeToken unexpected)) bounds)
        [] => Fail0 (B EOI NoBounds)
parseLetStatement _ _ ((B token bounds) :: _) _ _ =
  Fail0 (B (Expected ["let"] (describeToken token)) bounds)

||| Converts a valid target expression plus an assignment operator and value into a statement.
||| Only names, field access, and indexing can become assignment targets. The target
||| is normalized into a dedicated assignment-target AST node before the right-hand
||| expression is parsed. This parser also consumes the required trailing semicolon,
||| so callers resume directly at the next block item.
||| The caller has already consumed and classified the operator, and supplies its
||| bounds together with the tokens that follow it.
||| Tested by: `fn assign() {a[i] = 1; p.x = 2;}`.
parseAssignmentStatement :
     {0 root : List (Bounded Token)}
  -> SurfaceExpr
  -> (operator : AssignmentOperator)
  -> (operatorBounds : Bounds)
  -> NestedRule True SurfaceStatement root
parseAssignmentStatement targetExpression operator operatorBounds smaller nodeId
    afterOperator suffix _ =
  case assignmentTargetFromExpression targetExpression of
    Nothing =>
      failWithCustomError
        (ParseErrorWithMessage "Expression is not a valid assignment target.")
        operatorBounds
    Just targetValue =>
      let (statementNodeId, afterStatementNodeId) = reserveNodeId nodeId
          (targetNodeId, afterTargetNodeId) = reserveNodeId afterStatementNodeId
          (operatorNodeId, afterOperatorNodeId) = reserveNodeId afterTargetNodeId
          target = surfaceAstNode
            (MkAstInfo targetNodeId targetExpression.astInfo.span) targetValue
          locatedOperator = surfaceAstNode
            (MkAstInfo operatorNodeId (sourceSpan operatorBounds)) operator
       in case smaller CompleteExpression afterOperatorNodeId afterOperator suffix of
            Fail0 err => Fail0 err
            Succ0 (value, finalNodeId) afterValue =>
              case afterValue of
                (B (TokSym SymSemi) semiBounds) :: finalTokens =>
                  let assignment = MkAssignmentNode target locatedOperator value
                   in Succ0
                        (surfaceAstNode
                          (MkAstInfo statementNodeId
                            (mergeSpans targetExpression.astInfo.span
                              (sourceSpan semiBounds)))
                          (StatementAssignment assignment),
                         finalNodeId)
                        finalTokens
                (B unexpected unexpectedBounds) :: _ =>
                  Fail0 (B (Expected [";"] (describeToken unexpected)) unexpectedBounds)
                [] => Fail0 (B EOI NoBounds)

parseBlockContents _ _ _ _ _ [] _ _ = Fail0 (B EOI NoBounds)
parseBlockContents blockNodeId openBounds statements smaller nodeId
    ((B token bounds) :: remaining) suffix acc@(SA recur) =
  case token of
    TokSym SymRBrace =>
      let block = surfaceAstNode
            (MkAstInfo blockNodeId (sourceSpan (openBounds <+> bounds)))
            (MkBlockNode [] (statements <>> []) Nothing)
       in Succ0 (block, nodeId) remaining

    TokKw KwLet =>
      case parseLetStatement smaller nodeId (B token bounds :: remaining)
             suffix acc of
        Fail0 err => Fail0 err
        Succ0 (statement, nextNodeId) afterStatement @{statementSuffix} =>
          succT $
            parseBlockContents blockNodeId openBounds
              (statements :< statement) smaller nextNodeId afterStatement
              (suffixWithinStrict statementSuffix suffix)
              recur

    _ =>
      case smaller StatementStartExpression nodeId
             (B token bounds :: remaining) suffix of
        Fail0 err => Fail0 err
        Succ0 (expression, afterExpressionNodeId) afterExpression
              @{expressionSuffix} =>
          case afterExpression of
            [] => Fail0 (B EOI NoBounds)

            (B (TokSym SymSemi) semiBounds) :: afterSemi =>
              let (statementNodeId, nextNodeId) =
                    reserveNodeId afterExpressionNodeId
                  statement = surfaceAstNode
                    (MkAstInfo statementNodeId
                      (mergeSpans expression.astInfo.span (sourceSpan semiBounds)))
                    (StatementSemiExpression expression)
               in succT $
                    parseBlockContents blockNodeId openBounds
                      (statements :< statement) smaller nextNodeId afterSemi
                      (suffixWithinStrict (uncons expressionSuffix) suffix)
                      recur

            (B (TokSym SymRBrace) closeBounds) :: afterClose =>
              Succ0
                (surfaceAstNode
                  (MkAstInfo blockNodeId
                    (sourceSpan (openBounds <+> closeBounds)))
                  (MkBlockNode [] (statements <>> []) (Just expression)),
                 afterExpressionNodeId)
                afterClose

            (B nextToken nextBounds) :: afterNext =>
              if isBlockLikeExpression expression
                then
                  let (statementNodeId, nextNodeId) =
                        reserveNodeId afterExpressionNodeId
                      statement = surfaceAstNode
                        (MkAstInfo statementNodeId expression.astInfo.span)
                        (StatementExpression expression)
                   in succT $
                        parseBlockContents blockNodeId openBounds
                          (statements :< statement) smaller nextNodeId
                          (B nextToken nextBounds :: afterNext)
                          (suffixWithinStrict expressionSuffix suffix)
                          recur
                else
                  case nextToken of
                    TokSym symbol =>
                      case assignmentOperator symbol of
                        Just operator =>
                          case succT $
                                 parseAssignmentStatement expression operator
                                 nextBounds smaller afterExpressionNodeId afterNext
                                 (suffixWithinStrict
                                   (uncons expressionSuffix) suffix)
                                 recur of
                            Fail0 err => Fail0 err
                            Succ0 (statement, nextNodeId) afterStatement
                                  @{statementSuffix} =>
                              succT $
                                parseBlockContents blockNodeId openBounds
                                  (statements :< statement) smaller
                                  nextNodeId afterStatement
                                  (suffixWithinStrict statementSuffix suffix)
                                  recur
                        Nothing =>
                          failWithCustomError (ParseErrorWithMessage
                            "Expected `;` or `}`, found instead: `\{interpolate (TokSym symbol)}`.")
                            nextBounds

                    unexpected =>
                      failWithCustomError (ParseErrorWithMessage
                        "Expected `;` or `}`, found instead: `\{interpolate unexpected}`.")
                        nextBounds

parseBracedBlockWithin _ _ [] _ _ = Fail0 (B EOI NoBounds)
parseBracedBlockWithin smaller nodeId
    ((B (TokSym SymLBrace) bounds) :: remaining) suffix (SA recur) =
  let (blockNodeId, nextNodeId) = reserveNodeId nodeId
   in succT $
        parseBlockContents blockNodeId bounds [<] smaller nextNodeId remaining
          (trans (uncons Same) suffix) recur
parseBracedBlockWithin _ _ ((B token bounds) :: _) _ _ =
  failWithCustomError (ParseErrorWithMessage
    "Expected a braced block starting with `{`, found instead: `\{interpolate token}`.") bounds

parseBracedBlock nodeId tokens acc =
  parseBracedBlockWithin (expressionSmaller acc) nodeId tokens Same acc

||| Parses a `#[name]` or `#[name("argument")]` function attribute.
||| Tested by: `#[qasm_gate]\nfn empty() -> () {}` and
||| `#[qasm_def("qasm_subroutine_name")]\npub general fn empty() -> () {}`.
parseAttribute : Rule True SurfaceAttribute
parseAttribute _ [] _ = Fail0 (B EOI NoBounds)
parseAttribute nodeId
    (B (TokSym SymHash) hashBounds :: B (TokSym SymLBracket) _ ::
     B (TokIdent nameText) nameBounds ::
     B (TokSym SymRBracket) closeBounds :: remaining) _ =
  let (attributeNodeId, afterAttributeNodeId) = reserveNodeId nodeId
      (name, nextNodeId) = makeName nameText nameBounds afterAttributeNodeId
      attribute = surfaceAstNode
        (MkAstInfo attributeNodeId (sourceSpan (hashBounds <+> closeBounds)))
        (MkAttributeNode name Nothing)
   in Succ0 (attribute, nextNodeId) remaining
parseAttribute nodeId
    (B (TokSym SymHash) hashBounds :: B (TokSym SymLBracket) _ ::
     B (TokIdent nameText) nameBounds :: B (TokSym SymLParen) _ ::
     B (TokStringLitRaw rawText) argumentBounds :: B (TokSym SymRParen) _ ::
     B (TokSym SymRBracket) closeBounds :: remaining) _ =
  let (attributeNodeId, afterAttributeNodeId) = reserveNodeId nodeId
      (name, afterNameNodeId) = makeName nameText nameBounds afterAttributeNodeId
      (argumentNodeId, nextNodeId) = reserveNodeId afterNameNodeId
      argument = surfaceAstNode
        (MkAstInfo argumentNodeId (sourceSpan argumentBounds))
        (AttributeArgumentStringLit rawText)
      attribute = surfaceAstNode
        (MkAstInfo attributeNodeId (sourceSpan (hashBounds <+> closeBounds)))
        (MkAttributeNode name (Just [argument]))
   in Succ0 (attribute, nextNodeId) remaining
parseAttribute _ (B _ bounds :: _) _ =
  failWithCustomError (ParseErrorWithMessage "Malformed attribute.") bounds

||| Parses a function declaration from its modifiers through parameters, contracts, and body.
||| Modifiers and attributes are supplied by the top-level dispatchers; this function
||| starts immediately after the dispatcher-consumed `fn` token. It reserves the
||| function item node before parsing its children and threads the next free node ID
||| through every optional phase. The final item span starts at `declarationStart`,
||| so preceding attributes, visibility, `const`, or effects are included even though
||| they were parsed by another function.
||| Tested by: `const fn square(x: i64) -> i64 { x * x }`.
parseFunctionDeclaration :
    (itemNodeId : NodeId)
  -> (declarationStart : Bounds)
  -> (attributes : List SurfaceAttribute)
  -> (visibility : Maybe (SurfaceAstNode VisibilityQualifier))
  -> (constness : Maybe (SurfaceAstNode FunctionConstness))
  -> (functionEffect : Maybe (SurfaceAstNode FunctionEffect))
  -> Rule True SurfaceItem
parseFunctionDeclaration itemNodeId declarationStart attributes visibility
    constness functionEffect nodeId tokens acc =
  let Succ0 (functionName, afterNameNodeId) afterName :=
            parseName "function name" nodeId tokens acc
        | Fail0 err => Fail0 err
      Succ0 (functionParameters, afterParametersNodeId) afterParameters :=
            succT $ parseFunctionParameters afterNameNodeId afterName suffixAcc
        | Fail0 err => Fail0 err
      Succ0 (returnType, afterReturnTypeNodeId) afterReturnType :=
            succT $ parseOptionalReturnType
                      afterParametersNodeId afterParameters suffixAcc
        | Fail0 err => Fail0 err
      Succ0 (supportClause, afterSupportNodeId) afterSupport :=
            succT $ parseOptionalSupportClause
                      afterReturnTypeNodeId afterReturnType suffixAcc
        | Fail0 err => Fail0 err
      Succ0 (contractClauses, afterContractsNodeId) afterContracts :=
            succT $ parseContractClauses
                      afterSupportNodeId afterSupport suffixAcc
        | Fail0 err => Fail0 err
      Succ0 (functionBody, finalNodeId) finalTokens :=
            succT $ parseBracedBlock
                      afterContractsNodeId afterContracts suffixAcc
        | Fail0 err => Fail0 err
      declaration =
            MkFunctionDeclarationNode
              []                  -- docs
              attributes
              visibility
              constness
              functionEffect
              functionName
              functionParameters
              returnType
              supportClause
              contractClauses
              functionBody
      itemSpan =
            mergeSpans (sourceSpan declarationStart) functionBody.astInfo.span
   in Succ0
        (surfaceAstNode (MkAstInfo itemNodeId itemSpan) (ItemFunction declaration),
         finalNodeId)
        finalTokens

||| Parses a typed constant value declaration after its `const` prefix.
||| Tested by: `const N: i64 = 4;`.
parseConstantDeclaration :
    (itemNodeId : NodeId)
  -> (declarationStart : Bounds)
  -> (attributes : List SurfaceAttribute)
  -> (visibility : Maybe (SurfaceAstNode VisibilityQualifier))
  -> Rule True SurfaceItem
parseConstantDeclaration _ _ _ _ _ [] _ = Fail0 (B EOI NoBounds)
parseConstantDeclaration _ _ (_ :: _) _ _ ((B _ tokenBounds) :: _) _ =
  failWithCustomError
    (ParseErrorWithMessage "Attributes on const declarations are not yet supported.")
    tokenBounds
parseConstantDeclaration itemNodeId declarationStart [] visibility nodeId
    ((B token tokenBounds) :: remaining) acc =
  let Succ0 (constName, afterNameNodeId) afterName :=
            parseName "constant name" nodeId
              (B token tokenBounds :: remaining) acc
        | Fail0 err => Fail0 err
      (B (TokSym SymColon) _) :: afterColon := afterName
        | (B unexpected bounds) :: _ =>
            failWithCustomError
              (ParseErrorWithMessage
                "Expected `:` after constant name, found instead: `\{interpolate unexpected}`.")
              bounds
        | [] => Fail0 (B EOI NoBounds)
      Succ0 (constType, afterTypeNodeId) afterType :=
            succT $ parseType afterNameNodeId afterColon suffixAcc
        | Fail0 err => Fail0 err
      (B (TokSym SymEq) _) :: afterEquals := afterType
        | (B unexpected bounds) :: _ =>
            failWithCustomError
              (ParseErrorWithMessage
                "Expected `=` in const declaration, found instead: `\{interpolate unexpected}`.")
              bounds
        | [] => Fail0 (B EOI NoBounds)
      Succ0 (constValue, finalNodeId) afterValue :=
            succT $ parseExpression afterTypeNodeId afterEquals suffixAcc
        | Fail0 err => Fail0 err
      (B (TokSym SymSemi) semiBounds) :: finalTokens := afterValue
        | (B unexpected bounds) :: _ =>
            failWithCustomError
              (ParseErrorWithMessage
                "Expected `;` after const declaration, found instead: `\{interpolate unexpected}`.")
              bounds
        | [] => Fail0 (B EOI NoBounds)
      declaration = MkConstDeclarationNode [] visibility constName constType constValue
   in Succ0
        (surfaceAstNode
          (MkAstInfo itemNodeId (sourceSpan (declarationStart <+> semiBounds)))
          (ItemConst declaration),
         finalNodeId)
        finalTokens

||| Reports the common top-level error after all recognized prefixes have been read.
unexpectedTopLevelItem :
     {isStrict : Bool}
  -> {tokens : List (Bounded Token)}
  -> Token
  -> Bounds
  -> Res isStrict Token tokens CustomParseError a
unexpectedTopLevelItem token bounds =
  failWithCustomError
    (UnexpectedToken
      ("Unexpected token: `" ++ interpolate token ++
       "` at module level. Only function and constant declarations are currently supported."))
    bounds

||| Preserves the diagnostic associated with the most specific parsed item prefix.
invalidItemAfterPrefix :
     {isStrict : Bool}
  -> {tokens : List (Bounded Token)}
  -> ItemPrefix
  -> Token
  -> Bounds
  -> Res isStrict Token tokens CustomParseError a
invalidItemAfterPrefix itemPrefix token bounds =
  case itemPrefix.state of
    PrefixEffect _ locatedEffect =>
      failWithCustomError
        (ParseErrorWithMessage
          "Expected `fn` after `\{show locatedEffect.value}` effect modifier, found instead: `\{interpolate token}`.")
        bounds
    PrefixOrdinary visibility =>
      case visibility of
        Just _ =>
          failWithCustomError
            (ParseErrorWithMessage
              "Expected function or constant declaration after `pub` visibility modifier, found instead: `\{interpolate token}`.")
            bounds
        Nothing =>
          case itemPrefix.attributes of
            [<] => unexpectedTopLevelItem token bounds
            _ :< _ =>
              failWithCustomError
                (ParseErrorWithMessage
                  "Expected function declaration after attribute, found instead: `\{interpolate token}`.")
                bounds
    PrefixConst _ _ =>
      failWithCustomError
        (ParseErrorWithMessage
          "Expected a function or constant declaration after `const`, found instead: `\{interpolate token}`.")
        bounds
    PrefixConstEffect _ _ locatedEffect =>
      failWithCustomError
        (ParseErrorWithMessage
          "Expected `fn` after `\{show locatedEffect.value}` effect modifier, found instead: `\{interpolate token}`.")
        bounds

||| Dispatches the item keyword after attributes, visibility, constness, and effect
||| have been accumulated. This is the only top-level declaration dispatcher.
||| A `fn` keyword accepts every accumulated prefix; anything else is either the
||| name of a `const` value declaration or the most specific prefix diagnostic.
parseItemAfterPrefix : ItemPrefix -> Rule True SurfaceItem
parseItemAfterPrefix _ _ [] _ = Fail0 (B EOI NoBounds)
parseItemAfterPrefix itemPrefix nodeId
    ((B (TokKw KwFn) _) :: remaining) (SA recur) =
  let (visibility, constBounds, effect) = prefixComponents itemPrefix.state
      (constness, nextNodeId) = locatedConstness constBounds
   in succT $ parseFunctionDeclaration
        itemPrefix.itemNodeId itemPrefix.declarationStart
        (itemPrefix.attributes <>> []) visibility constness effect nextNodeId
        remaining recur
  where
    locatedConstness :
      Maybe Bounds -> (Maybe (SurfaceAstNode FunctionConstness), Nat)
    locatedConstness Nothing = (Nothing, nodeId)
    locatedConstness (Just constBounds) =
      let (constnessNodeId, nextNodeId) = reserveNodeId nodeId
       in ( Just (surfaceAstNode
              (MkAstInfo constnessNodeId (sourceSpan constBounds)) ConstFunction)
          , nextNodeId)
parseItemAfterPrefix itemPrefix nodeId
    ((B token bounds) :: remaining) acc =
  case itemPrefix.state of
    PrefixConst visibility _ =>
      parseConstantDeclaration itemPrefix.itemNodeId itemPrefix.declarationStart
        (itemPrefix.attributes <>> []) visibility nodeId
        (B token bounds :: remaining) acc
    _ =>
      case token of
        TokKw keyword =>
          case unsupportedTopLevelItem keyword of
            Just err => failWithCustomError err bounds
            Nothing => invalidItemAfterPrefix itemPrefix token bounds
        _ => invalidItemAfterPrefix itemPrefix token bounds

||| Collects the ordered prefix of a top-level declaration. Attributes must precede
||| visibility, which must precede constness or a function effect; duplicate or
||| misplaced modifiers fall through to the terminal dispatcher and are rejected.
parseItemPrefix : ItemPrefix -> Rule True SurfaceItem
parseItemPrefix _ _ [] _ = Fail0 (B EOI NoBounds)
parseItemPrefix itemPrefix nodeId
    ((B token bounds) :: remaining) acc@(SA recur) =
  case token of
    TokOuterDoc _ =>
      failWithCustomError
        (UnsupportedFeature "Outer doc comments are not yet supported.") bounds

    TokInnerDoc _ =>
      failWithCustomError
        (UnsupportedFeature "Inner doc comments are not yet supported.") bounds

    TokSym SymHash =>
      case itemPrefix.state of
        PrefixOrdinary Nothing =>
          case parseAttribute nodeId
                 (B (TokSym SymHash) bounds :: remaining) acc of
            Fail0 err => Fail0 err
            Succ0 (attribute, nextNodeId) afterAttribute =>
              let nextPrefix =
                    { attributes := itemPrefix.attributes :< attribute } itemPrefix
               in succT $
                    parseItemPrefix nextPrefix nextNodeId afterAttribute recur
        _ => parseItemAfterPrefix itemPrefix nodeId
               (B (TokSym SymHash) bounds :: remaining) acc

    TokKw KwPub =>
      case itemPrefix.state of
        PrefixOrdinary Nothing =>
          let (visibilityNodeId, nextNodeId) = reserveNodeId nodeId
              locatedVisibility = surfaceAstNode
                (MkAstInfo visibilityNodeId (sourceSpan bounds)) VisibilityPublic
              nextPrefix =
                { state := PrefixOrdinary (Just locatedVisibility) } itemPrefix
           in succT $ parseItemPrefix nextPrefix nextNodeId remaining recur
        _ => parseItemAfterPrefix itemPrefix nodeId
               (B (TokKw KwPub) bounds :: remaining) acc

    TokKw KwConst =>
      case itemPrefix.state of
        PrefixOrdinary visibility =>
          let nextPrefix = { state := PrefixConst visibility bounds } itemPrefix
           in succT $ parseItemPrefix nextPrefix nodeId remaining recur
        _ => parseItemAfterPrefix itemPrefix nodeId
               (B (TokKw KwConst) bounds :: remaining) acc

    TokKw keyword =>
      case (itemPrefix.state, functionEffectFromKeyword keyword) of
        (PrefixOrdinary visibility, Just effectValue) =>
          let (effectNodeId, nextNodeId) = reserveNodeId nodeId
              locatedEffect = surfaceAstNode
                (MkAstInfo effectNodeId (sourceSpan bounds)) effectValue
              nextPrefix = { state := PrefixEffect visibility locatedEffect } itemPrefix
           in succT $ parseItemPrefix nextPrefix nextNodeId remaining recur
        (PrefixConst visibility constBounds, Just effectValue) =>
          let (effectNodeId, nextNodeId) = reserveNodeId nodeId
              locatedEffect = surfaceAstNode
                (MkAstInfo effectNodeId (sourceSpan bounds)) effectValue
              nextPrefix =
                { state := PrefixConstEffect visibility constBounds locatedEffect }
                  itemPrefix
           in succT $ parseItemPrefix nextPrefix nextNodeId remaining recur
        _ => parseItemAfterPrefix itemPrefix nodeId
               (B (TokKw keyword) bounds :: remaining) acc

    _ => parseItemAfterPrefix itemPrefix nodeId
           (B token bounds :: remaining) acc

||| Parses one top-level item by collecting its prefix and dispatching once.
||| Tested by:
||| `const N: i64 = 4;`,
||| `pub unitary fn empty() {}`
||| `#[qasm_gate] pub fn annotated() {}`.
parseItem : Rule True SurfaceItem
parseItem _ [] _ = Fail0 (B EOI NoBounds)
parseItem nodeId ((B firstToken startBounds) :: remaining) acc =
  let (itemNodeId, nextNodeId) = reserveNodeId nodeId
   in parseItemPrefix
        (MkItemPrefix itemNodeId startBounds [<] (PrefixOrdinary Nothing))
        nextNodeId (B firstToken startBounds :: remaining) acc

||| Parses top-level items until end of input while preserving source order.
||| Items accumulate in a `SnocList` and are converted once at EOF. A valid lexer
||| stream must contain exactly one final `TokEOF`; missing EOF or tokens following
||| EOF are rejected. Each iteration resumes with both the remaining suffix and the
||| next free node ID returned by `parseItem`.
||| Tested by:
||| `const N: i64 = 4;\nfn arrays() { let c: [i32; N]; }`.
parseItems : SnocList SurfaceItem -> Rule True (List SurfaceItem)
parseItems _ _ [] _ =
    Fail0 (B EOI NoBounds)  -- every valid token stream must contain TokEOF
parseItems items nextNodeId [B TokEOF _] _ =
    Succ0 (items <>> [], nextNodeId) []
parseItems _ _ ((B TokEOF _) :: (B _ bounds) :: _) _ =
    Fail0 (B EOI bounds)
parseItems items nextNodeId tokens acc@(SA recur) =
    case parseItem nextNodeId tokens acc of
        Fail0 err =>
            Fail0 err

        Succ0 (item, followingNodeId) remaining =>
            succT $ parseItems (items :< item) followingNodeId remaining recur

||| Parses all items into a source-file AST spanning the file being parsed.
parseModule : Rule True SurfaceSourceFile
parseModule firstItemNodeId tokens acc =
    case parseItems [<] firstItemNodeId tokens acc of
        Fail0 err =>
            Fail0 err

        Succ0 (items, nextNodeId) remaining =>
            Succ0
                ( surfaceAstNode
                    (sourceFileInfo (MkNodeId 0 0) items)           -- source file node id is always 0, 0
                    (MkSourceFileNode [] items)                     -- inner doc comments are not yet supported
                , nextNodeId
                )
                remaining

---------------------------------------------------------------------------------------------------
-- Main entry point: parse file using the idris2-parser library's machinery from Text.Parse.Manual
---------------------------------------------------------------------------------------------------

||| Attaches a converted source span, which carries the filename, to a parser error.
||| Tested by the malformed input `fn empty(); }`.
locatedParseError : SourceFileName => Bounds -> ParseError -> Located ParseError
locatedParseError bounds parseError =
    MkLocated (sourceSpan bounds) parseError

public export
||| Runs the module parser over a token stream and returns either a located error or source file.
||| Node ID zero is reserved for the source-file node, so item allocation begins at
||| one. Parser failures are enriched with the filename here. `parseItems` consumes
||| the complete token stream whenever it succeeds, so a successful module parse
||| with leftover tokens indicates an internal parser invariant violation.
parseFile : String -> List (Bounded Token) -> Either (Located ParseError) SurfaceSourceFile
parseFile fileName tokens =
    let sourceFileName = MkSourceFileName fileName in
    case parseModule @{sourceFileName} 1 tokens suffixAcc of   -- first item node id is 1 (0 is source file node id)
        Fail0 (B err bounds) =>
            Left (locatedParseError @{sourceFileName} bounds err)

        Succ0 (sourceFile, _) [] =>
            Right sourceFile

        Succ0 _ (_ :: _) =>
            assert_total $ idris_crash
                "parseFile: parseModule function succeeded without consuming the complete token stream."
