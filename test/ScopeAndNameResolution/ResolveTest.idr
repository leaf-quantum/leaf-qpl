module ScopeAndNameResolution.ResolveTest

import Compiler.ScopeAndNameResolution.Data
import Frontend.ASTData
import Frontend.ASTPhases
import Frontend.Source
import Frontend.Syntax.AST
import Frontend.Syntax.Common
import Frontend.Syntax.Name
import Frontend.Syntax.Operator
import Frontend.Syntax.Pattern
import Frontend.Syntax.Type
import ScopeAndNameResolution.Helper
import ScopeAndNameResolution.ResolveTestHelper

import Data.List
import Data.List1
import Data.Maybe
import Data.SnocList
import Data.SortedMap
import Test.Simple

%default total

export
runSymbolAndScopeResolutionTests : IO ()
runSymbolAndScopeResolutionTests = runTests $ Test.do
  test "duplicate declaration diagnostics report both source positions" $
    show (ResolutionFailure (DuplicateDeclaration "f" [MkSymbolId 42]
      (MkSourceSpan "resolution-test.lf" (MkSourcePos 3 4) (MkSourcePos 3 5))
      (MkSourceSpan "resolution-test.lf" (MkSourcePos 1 7) (MkSourcePos 1 8))))
      `shouldBe` "Resolution: duplicate f at 3:4; previous declaration at 1:7"

  test "inaccessible symbol diagnostics report the symbol name" $
    show (ResolutionFailure (InaccessibleSymbol "privateFunction" (MkSymbolId 42)
      (MkSourceSpan "resolution-test.lf" (MkSourcePos 3 7) (MkSourcePos 3 22))))
      `shouldBe` "Resolution: inaccessible symbol privateFunction at 3:7"

  test "declarations, reads and writes agree between AST and reference tables" $
    checkSource "fn f() { let mut x = 1; let y = x; x = y; x; }" (\resolved => do
      (_, fn) <- functionNamed "f" resolved
      xBinding <- letAt 0 fn.functionBody
      yBinding <- letAt 1 fn.functionBody
      x <- binder xBinding.letPattern
      y <- binder yBinding.letPattern
      xRead <- initializer yBinding
      statement <- at 2 fn.functionBody.value.blockStatements
      StatementAssignment assignment <- pure statement.value | _ => Nothing
      AssignTargetName target <- pure assignment.assignmentTarget.value | _ => Nothing
      finalRead <- exprAt 3 fn.functionBody
      readsX <- useMatches resolved x xRead
      readsY <- useMatches resolved y assignment.assignmentValue
      finalX <- useMatches resolved x finalRead
      scope <- scopeFor resolved fn.functionBody
      xRefs <- lookup (symbolId x) resolved.tables.references
      yRefs <- lookup (symbolId y) resolved.tables.references
      pure (symbolId x /= symbolId y && symbolId target == symbolId x &&
            readsX && readsY && finalX &&
            referenceMatches resolved DeclarationReference xBinding.letPattern.astInfo.nodeId x &&
            referenceMatches resolved DeclarationReference yBinding.letPattern.astInfo.nodeId y &&
            referenceMatches resolved AssignmentTarget assignment.assignmentTarget.astInfo.nodeId target &&
            length (xRefs <>> []) == 4 && length (yRefs <>> []) == 2 &&
            bindingMatches scope x && bindingMatches scope y &&
            all (\statement => lookup statement.astInfo.nodeId resolved.tables.nodeScopes == Just scope.id)
              fn.functionBody.value.blockStatements &&
            (scope.declaredSymbolsInOrder <>> []) == [symbolId x, symbolId y] &&
            symbolMatches resolved x scope.id "local" x.astInfo &&
            symbolMatches resolved y scope.id "local" y.astInfo &&
            localMatches resolved x True && localMatches resolved y False)) `shouldBe` Right True

  test "same-scope shadowing resolves initializer uses to the previous declaration" $
    checkSource "fn f() { let x = 1; let x = x + 1; x; }" (\resolved => do
      (_, fn) <- functionNamed "f" resolved
      firstBinding <- letAt 0 fn.functionBody
      secondBinding <- letAt 1 fn.functionBody
      first <- binder firstBinding.letPattern
      second <- binder secondBinding.letPattern
      init <- initializer secondBinding
      ExprBinary _ left _ <- pure init.value | _ => Nothing
      usesFirst <- useMatches resolved first left
      final <- exprAt 2 fn.functionBody
      usesSecond <- useMatches resolved second final
      scope <- scopeFor resolved fn.functionBody
      pure (symbolId first /= symbolId second && usesFirst && usesSecond &&
            bindingMatches scope second &&
            (scope.declaredSymbolsInOrder <>> []) == [symbolId first, symbolId second] &&
            isJust (lookup (symbolId first) resolved.tables.symbols))) `shouldBe` Right True

  -- A function, unlike a constant, is not a pattern, so a local may shadow it.
  test "array-size annotations use the outer function before introducing a local" $
    checkSource "const fn n() -> i32 { 2 } fn f() { let n: [i32; n()] = [0, 0]; n; }" (\resolved => do
      (_, size) <- functionNamed "n" resolved
      (_, fn) <- functionNamed "f" resolved
      binding <- letAt 0 fn.functionBody
      local <- binder binding.letPattern
      ty <- binding.letTypeAnnotation
      TyArray _ count <- pure ty.value | _ => Nothing
      ExprCall callee [] <- pure count.value | _ => Nothing
      sizeUsesFunction <- useMatches resolved size.functionName callee
      final <- exprAt 1 fn.functionBody
      finalUsesLocal <- useMatches resolved local final
      pure (symbolId size.functionName /= symbolId local && sizeUsesFunction && finalUsesLocal)) `shouldBe` Right True

  test "nested block final expressions use inner bindings and restore the outer scope" $
    checkSource "fn f() { let x = 1; let y = { let x = 2; x }; x; }" (\resolved => do
      (_, fn) <- functionNamed "f" resolved
      outerBinding <- letAt 0 fn.functionBody
      outerName <- binder outerBinding.letPattern
      y <- letAt 1 fn.functionBody
      init <- initializer y
      block <- blockBody init
      innerBinding <- letAt 0 block
      innerName <- binder innerBinding.letPattern
      final <- block.value.finalExpression
      innerUse <- useMatches resolved innerName final
      after <- exprAt 2 fn.functionBody
      outerUse <- useMatches resolved outerName after
      outer <- scopeFor resolved fn.functionBody
      inner <- scopeFor resolved block
      pure (symbolId innerName /= symbolId outerName && innerUse && outerUse &&
            isBlock inner && inner.parent == Just outer.id &&
            bindingMatches outer outerName && bindingMatches inner innerName)) `shouldBe` Right True

  test "forward calls, recursion and mutual recursion reuse function declaration IDs" $
    checkSource "fn first() { second(); first(); } fn second() { first(); }" (\resolved => do
      (firstInfo, first) <- functionNamed "first" resolved
      (secondInfo, second) <- functionNamed "second" resolved
      forwardCall <- exprAt 0 first.functionBody
      recursiveCall <- exprAt 1 first.functionBody
      mutualCall <- exprAt 0 second.functionBody
      ExprCall forward [] <- pure forwardCall.value | _ => Nothing
      ExprCall recursive [] <- pure recursiveCall.value | _ => Nothing
      ExprCall mutualCallee [] <- pure mutualCall.value | _ => Nothing
      forwardOK <- useMatches resolved second.functionName forward
      recursiveOK <- useMatches resolved first.functionName recursive
      mutualOK <- useMatches resolved first.functionName mutualCallee
      pure (forwardOK && recursiveOK && mutualOK &&
            symbolId first.functionName /= symbolId second.functionName &&
            referenceMatches resolved DeclarationReference firstInfo.nodeId first.functionName &&
            referenceMatches resolved DeclarationReference secondInfo.nodeId second.functionName)) `shouldBe` Right True

  test "parameter metadata and bindings are complete and isolated between functions" $
    checkSource "fn f(mut x: i32, y: i32) { let z = x; y; } fn g(x: i32) { x; }" (\resolved => do
      (_, f) <- functionNamed "f" resolved
      (_, g) <- functionNamed "g" resolved
      [xp, yp] <- pure f.functionParameters | _ => Nothing
      [gp] <- pure g.functionParameters | _ => Nothing
      NormalParameter _ _ x _ <- pure xp.value | _ => Nothing
      NormalParameter _ _ y _ <- pure yp.value | _ => Nothing
      NormalParameter _ _ gx _ <- pure gp.value | _ => Nothing
      fScope <- scopeFor resolved xp
      gScope <- scopeFor resolved gp
      fBody <- scopeFor resolved f.functionBody
      zBinding <- letAt 0 f.functionBody
      z <- binder zBinding.letPattern
      init <- initializer zBinding
      xOK <- useMatches resolved x init
      yExpr <- exprAt 1 f.functionBody
      yOK <- useMatches resolved y yExpr
      gxExpr <- exprAt 0 g.functionBody
      gxOK <- useMatches resolved gx gxExpr
      pure (xOK && yOK && gxOK && symbolId x /= symbolId gx &&
            fScope.id /= gScope.id && fBody.parent == Just fScope.id &&
            fScope.parent == Just resolved.rootScope && gScope.parent == Just resolved.rootScope &&
            (case fScope.kind of FunctionScope => True; _ => False) &&
            (case gScope.kind of FunctionScope => True; _ => False) &&
            bindingMatches fScope x && bindingMatches fScope y && bindingMatches gScope gx &&
            (fScope.declaredSymbolsInOrder <>> []) == [symbolId x, symbolId y] &&
            localMatches resolved x True && localMatches resolved y False &&
            localMatches resolved gx False && localMatches resolved z False &&
            symbolMatches resolved x fScope.id "parameter" x.astInfo &&
            referenceMatches resolved DeclarationReference xp.astInfo.nodeId x &&
            referenceMatches resolved DeclarationReference yp.astInfo.nodeId y &&
            referenceMatches resolved DeclarationReference gp.astInfo.nodeId gx)) `shouldBe` Right True

  test "destructuring registers each binder with its own mutability and ignores wildcards" $
    checkSource "fn f() { let (mut a, (_, b)) = (1, (2, 3)); let [mut c, _, d] = [4, 5, 6]; a; b; c; d; }" (\resolved => do
      (_, fn) <- functionNamed "f" resolved
      tuple <- letAt 0 fn.functionBody
      array <- letAt 1 fn.functionBody
      let binders = patternBinders tuple.letPattern ++ patternBinders array.letPattern
      let names = map snd binders
      uses <- traverse (\i => exprAt i fn.functionBody) [2, 3, 4, 5]
      matches <- traverse (\(name, use) => useMatches resolved name use) (zip names uses)
      scope <- scopeFor resolved fn.functionBody
      pure (map (\name => name.value.resolvedNameNodeText) names == ["a", "b", "c", "d"] &&
            length (nub (map symbolId names)) == 4 && all id matches &&
            all (\(name, mutable) => localMatches resolved name mutable) (zip names [True, False, True, False]) &&
            all (\(pattern, name) => referenceMatches resolved DeclarationReference pattern.astInfo.nodeId name) binders &&
            all (bindingMatches scope) names &&
            (scope.declaredSymbolsInOrder <>> []) == map symbolId names &&
            isNothing (lookup "_" scope.valueBindings))) `shouldBe` Right True

  test "for iterator and trailing uses resolve outside the loop binder's scope" $
    checkSource "fn f() { let x = [1]; for x in x { x; } x; }" (\resolved => do
      (_, fn) <- functionNamed "f" resolved
      binding <- letAt 0 fn.functionBody
      outerName <- binder binding.letPattern
      loop <- exprAt 1 fn.functionBody
      ExprFor pattern iterator body <- pure loop.value | _ => Nothing
      loopName <- binder pattern
      outer <- scopeFor resolved fn.functionBody
      loopScope <- scopeFor resolved pattern
      bodyScope <- scopeFor resolved body
      iteratorOK <- useMatches resolved outerName iterator
      bodyUse <- exprAt 0 body
      bodyOK <- useMatches resolved loopName bodyUse
      after <- exprAt 2 fn.functionBody
      afterOK <- useMatches resolved outerName after
      pure (iteratorOK && bodyOK && afterOK && symbolId outerName /= symbolId loopName &&
            (case loopScope.kind of ForScope => True; _ => False) &&
            loopScope.parent == Just outer.id && bodyScope.parent == Just loopScope.id && isBlock bodyScope &&
            bindingMatches outer outerName && bindingMatches loopScope loopName &&
            lookup loop.astInfo.nodeId resolved.tables.nodeScopes == Just outer.id &&
            referenceMatches resolved DeclarationReference pattern.astInfo.nodeId loopName &&
            localMatches resolved loopName False)) `shouldBe` Right True

  test "if and else-if branch scopes are siblings and chained-if nodes retain the enclosing scope" $
    checkSource "fn f(flag: bool) { if flag { let x = 1; x; } else if flag { let x = 2; x; } else { let x = 3; x; } flag; }" (\resolved => do
      (_, fn) <- functionNamed "f" resolved
      [MkAstNode _ _ (NormalParameter _ _ flag _)] <- pure fn.functionParameters | _ => Nothing
      expression <- exprAt 0 fn.functionBody
      ExprIf first <- pure expression.value | _ => Nothing
      ElseChainedIf chained <- first.ifElseBranch | _ => Nothing
      ElseBlock last <- chained.value.ifElseBranch | _ => Nothing
      let blocks = [first.ifThenBlock, chained.value.ifThenBlock, last]
      scopes <- traverse (scopeFor resolved) blocks
      bindings <- traverse (letAt 0) blocks
      names <- traverse (binder . (.letPattern)) bindings
      uses <- traverse (exprAt 1) blocks
      matches <- traverse (\(name, use) => useMatches resolved name use) (zip names uses)
      firstCondition <- useMatches resolved flag first.ifCondition
      secondCondition <- useMatches resolved flag chained.value.ifCondition
      outer <- scopeFor resolved fn.functionBody
      after <- exprAt 1 fn.functionBody
      afterOK <- useMatches resolved flag after
      pure (firstCondition && secondCondition && afterOK && all id matches &&
            length (nub (map (.id) scopes)) == 3 && length (nub (map symbolId names)) == 3 &&
            all (\scope => isBlock scope && scope.parent == Just outer.id) scopes &&
            all (\(scope, name) => bindingMatches scope name) (zip scopes names) &&
            lookup chained.astInfo.nodeId resolved.tables.nodeScopes == Just outer.id &&
            isNothing (lookup "x" outer.valueBindings))) `shouldBe` Right True

  test "plain blocks isolate declarations" $ blockIsolation "" `shouldBe` Right True
  test "loop blocks isolate declarations" $ blockIsolation "loop" `shouldBe` Right True
  test "while blocks isolate declarations" $ blockIsolation "while true" `shouldBe` Right True
  test "controlled blocks isolate declarations" $ blockIsolation "ctrl(&q)" `shouldBe` Right True
  test "adjoint blocks isolate declarations" $ blockIsolation "adjoint" `shouldBe` Right True

  test "controlled and adjoint callables resolve their controls and function names" $
    checkSource "unitary fn g(q: &qubit) {} unitary fn f(q: &qubit) { ctrl(q).apply(g); adjoint(g); }" (\resolved => do
      (_, g) <- functionNamed "g" resolved
      (_, f) <- functionNamed "f" resolved
      [MkAstNode _ _ (NormalParameter _ _ q _)] <- pure f.functionParameters | _ => Nothing
      controlled <- exprAt 0 f.functionBody
      adjointed <- exprAt 1 f.functionBody
      ExprCtrl (ControlledCallable (control ::: []) _ callable) <- pure controlled.value | _ => Nothing
      ExprAdjoint (AdjointOfCallable adjointCallable) <- pure adjointed.value | _ => Nothing
      controlOK <- useMatches resolved q control
      callableOK <- useMatches resolved g.functionName callable
      adjointOK <- useMatches resolved g.functionName adjointCallable
      bodyScope <- scopeFor resolved f.functionBody
      pure (controlOK && callableOK && adjointOK &&
            lookup controlled.astInfo.nodeId resolved.tables.nodeScopes == Just bodyScope.id &&
            lookup adjointed.astInfo.nodeId resolved.tables.nodeScopes == Just bodyScope.id)) `shouldBe` Right True

  test "parameter and return annotations see module functions before parameter bindings" $
    checkSource "const fn n() -> i32 { 2 } fn f(n: i32, values: [i32; n()]) -> [i32; n()] { values }" (\resolved => do
      (_, size) <- functionNamed "n" resolved
      (_, fn) <- functionNamed "f" resolved
      [_, MkAstNode _ _ (NormalParameter _ _ _ arrayType)] <- pure fn.functionParameters | _ => Nothing
      resultType <- fn.returnType
      TyArray _ parameterSize <- pure arrayType.value | _ => Nothing
      TyArray _ resultSize <- pure resultType.value | _ => Nothing
      ExprCall parameterCallee [] <- pure parameterSize.value | _ => Nothing
      ExprCall resultCallee [] <- pure resultSize.value | _ => Nothing
      parameterOK <- useMatches resolved size.functionName parameterCallee
      resultOK <- useMatches resolved size.functionName resultCallee
      pure (parameterOK && resultOK)) `shouldBe` Right True

  test "functions and constants have module ownership and no local-variable metadata" $
    checkSource "pub const n: i32 = 1; pub fn f() { n; } fn g() {}" (\resolved => do
      (constInfo, con) <- constantNamed "n" resolved
      (fnInfo, fn) <- functionNamed "f" resolved
      (_, privateFn) <- functionNamed "g" resolved
      constantSymbol <- lookup (symbolId con.constName) resolved.tables.symbols
      functionSymbol <- lookup (symbolId fn.functionName) resolved.tables.symbols
      privateSymbol <- lookup (symbolId privateFn.functionName) resolved.tables.symbols
      use <- exprAt 0 fn.functionBody
      useOK <- useMatches resolved con.constName use
      pure (useOK && symbolMatches resolved con.constName resolved.rootScope "constant" constInfo &&
            symbolMatches resolved fn.functionName resolved.rootScope "function" fnInfo &&
            (case constantSymbol.visibility of PublicVisibility => True; _ => False) &&
            (case functionSymbol.visibility of PublicVisibility => True; _ => False) &&
            (case privateSymbol.visibility of ModuleVisibility => True; _ => False) &&
            all (\name => isNothing (lookup (symbolId name) resolved.tables.localVariables))
              [con.constName, fn.functionName, privateFn.functionName] &&
            resolved.tables.currentScope == resolved.rootScope &&
            resolved.tables.currentModule == resolved.rootModule &&
            (case resolved.tables.currentScopeKind of ModuleScope => True; _ => False))) `shouldBe` Right True

  test "self-initialization without an outer binding is unresolved" $
    unresolved "fn f() { let x = x; }" "x" `shouldBe` Right True
  test "a use before a later local declaration is unresolved" $
    unresolved "fn f() { x; let x = 1; }" "x" `shouldBe` Right True
  test "a block local cannot escape its block" $
    unresolved "fn f() { { let x = 1; } x; }" "x" `shouldBe` Right True
  test "a then-branch local is unavailable in the else branch" $
    unresolved "fn f() { if true { let x = 1; } else { x; } }" "x" `shouldBe` Right True
  test "a for binder cannot escape its loop" $
    unresolved "fn f() { for x in [1] {} x; }" "x" `shouldBe` Right True
  test "a parameter is unavailable in another function" $
    unresolved "fn f(x: i32) {} fn g() { x; }" "x" `shouldBe` Right True
  test "controlled block locals cannot escape" $
    unresolved "fn f(q: qubit) { ctrl(&q) { let x = 1; } x; }" "x" `shouldBe` Right True
  test "adjoint block locals cannot escape" $
    unresolved "fn f() { adjoint { let x = 1; } x; }" "x" `shouldBe` Right True

  test "unresolved-name diagnostics identify the exact source occurrence" $
    (case resolveSource "fn f() {\n  missing;\n}" of
       Left (ResolutionFailure (UnresolvedName name span)) =>
         Right (name, coordinates span)
       Left err => Left (show err)
       Right _ => Left "Expected UnresolvedName")
      `shouldBe` Right ("missing", (2, 3, 2, 10))

  test "duplicate function diagnostics identify both declarations" $
    (case resolveSource "fn f() {}\nfn f() {}" of
       Left (ResolutionFailure (DuplicateDeclaration name [_] span previousSpan)) =>
         Right (name, spanKey span, spanKey previousSpan)
       Left err => Left (show err)
       Right _ => Left "Expected DuplicateDeclaration")
      `shouldBe` Right ("f", ("", 2, 4, 2, 5), ("", 1, 4, 1, 5))

  test "constants and functions conflict in the same value namespace" $
    (case resolveSource "const f: i32 = 1;\nfn f() {}" of
       Left (ResolutionFailure (DuplicateDeclaration name [_] span previousSpan)) =>
         Right (name, spanKey span, spanKey previousSpan)
       Left err => Left (show err)
       Right _ => Left "Expected DuplicateDeclaration")
      `shouldBe` Right ("f", ("", 2, 4, 2, 5), ("", 1, 7, 1, 8))

  test "call callee and every argument have value references in the body scope" $
    expressionUses "g(x, n)" ["g", "x", "n"] (\expression => case expression.value of
      ExprCall callee arguments => Just (callee :: arguments)
      _ => Nothing) `shouldBe` Right True

  test "tuple elements resolve each name occurrence" $
    expressionUses "(x, n)" ["x", "n"] (\expression => case expression.value of
      ExprTuple elements => Just (forget elements)
      _ => Nothing) `shouldBe` Right True

  test "array elements resolve each name occurrence" $
    expressionUses "[x, n]" ["x", "n"] (\expression => case expression.value of
      ExprArray elements => Just elements
      _ => Nothing) `shouldBe` Right True

  test "repeated arrays resolve both their element and count" $
    expressionUses "[x; n]" ["x", "n"] (\expression => case expression.value of
      ExprRepeatedArray element count => Just [element, count]
      _ => Nothing) `shouldBe` Right True

  test "indexing resolves the object and the index" $
    expressionUses "a[i]" ["a", "i"] (\expression => case expression.value of
      ExprIndex object index => Just [object, index]
      _ => Nothing) `shouldBe` Right True

  test "ranges resolve both endpoints" $
    expressionUses "i..n" ["i", "n"] (\expression => case expression.value of
      ExprRange (Just start) _ (Just end) => Just [start, end]
      _ => Nothing) `shouldBe` Right True

  test "ranges without an upper bound resolve their start" $
    expressionUses "i.." ["i"] (\expression => case expression.value of
      ExprRange (Just start) _ Nothing => Just [start]
      _ => Nothing) `shouldBe` Right True

  test "ranges without a lower bound resolve their end" $
    expressionUses "..n" ["n"] (\expression => case expression.value of
      ExprRange Nothing _ (Just end) => Just [end]
      _ => Nothing) `shouldBe` Right True

  test "unary operands retain their reference and enclosing scope" $
    expressionUses "-x" ["x"] (\expression => case expression.value of
      ExprUnary _ operand => Just [operand]
      _ => Nothing) `shouldBe` Right True

  test "both binary operands retain their references and enclosing scope" $
    expressionUses "x + n" ["x", "n"] (\expression => case expression.value of
      ExprBinary _ left right => Just [left, right]
      _ => Nothing) `shouldBe` Right True

  test "casts resolve their operand and expressions in the target type" $
    expressionUses "a as [i32; n]" ["a", "n"] (\expression => do
      ExprCast operand target <- pure expression.value | _ => Nothing
      TyArray _ size <- pure target.value | _ => Nothing
      pure [operand, size]) `shouldBe` Right True

  test "tuple indexing resolves its base expression" $
    expressionUses "pair.0" ["pair"] (\expression => case expression.value of
      ExprTupleIndex tuple "0" => Just [tuple]
      _ => Nothing) `shouldBe` Right True

  test "indexed assignment records reads of the base, index and value" $
    checkSource "fn f(mut a: [i32; 2], i: i32, x: i32) { a[i] = x; }" (\resolved => do
      (_, fn) <- functionNamed "f" resolved
      [a, i, x] <- parameterNames fn | _ => Nothing
      assignment <- assignmentAt 0 fn.functionBody
      AssignTargetIndex object index <- pure assignment.assignmentTarget.value | _ => Nothing
      scope <- scopeFor resolved fn.functionBody
      reads <- usesInScope resolved scope.id [(a, object), (i, index), (x, assignment.assignmentValue)]
      pure (reads && nodeHasScope resolved scope.id assignment.assignmentTarget &&
            length (valueReferences resolved) == 3 && length (allReferences resolved) == 7)) `shouldBe` Right True

  test "tuple-index assignment records reads without inventing a symbol for the index" $
    checkSource "fn f(mut pair: (i32, i32), x: i32) { pair.0 = x; }" (\resolved => do
      (_, fn) <- functionNamed "f" resolved
      [pair, x] <- parameterNames fn | _ => Nothing
      assignment <- assignmentAt 0 fn.functionBody
      AssignTargetTupleIndex object "0" <- pure assignment.assignmentTarget.value | _ => Nothing
      scope <- scopeFor resolved fn.functionBody
      reads <- usesInScope resolved scope.id [(pair, object), (x, assignment.assignmentValue)]
      pure (reads && nodeHasScope resolved scope.id assignment.assignmentTarget &&
            length (valueReferences resolved) == 2 && length (allReferences resolved) == 5)) `shouldBe` Right True

  -- Member validity is deferred to typechecking; resolution still visits the
  -- base and value and records the textual selector's lexical scope.
  test "field assignment records the selector scope while deferring member lookup" $
    checkSource "fn f(mut pair: (i32, i32), x: i32) { pair.field = x; }" (\resolved => do
      (_, fn) <- functionNamed "f" resolved
      [pair, x] <- parameterNames fn | _ => Nothing
      assignment <- assignmentAt 0 fn.functionBody
      AssignTargetField object field <- pure assignment.assignmentTarget.value | _ => Nothing
      scope <- scopeFor resolved fn.functionBody
      reads <- usesInScope resolved scope.id [(pair, object), (x, assignment.assignmentValue)]
      pure (reads && nodeHasScope resolved scope.id assignment.assignmentTarget &&
            nodeHasScope resolved scope.id field &&
            all (\ref => ref.occurrence.nodeId /= field.astInfo.nodeId) (allReferences resolved) &&
            not (elem "field" (map (.declaredName) (sourceSymbols resolved))) &&
            length (allReferences resolved) == 5)) `shouldBe` Right True

  test "compound assignment resolves its write and both reads after desugaring" $
    checkSource "fn f(mut x: i32, y: i32) { x += y; }" (\resolved => do
      (fnInfo, fn) <- functionNamed "f" resolved
      [xp, yp] <- pure fn.functionParameters | _ => Nothing
      [x, y] <- parameterNames fn | _ => Nothing
      assignment <- assignmentAt 0 fn.functionBody
      AssignTargetName target <- pure assignment.assignmentTarget.value | _ => Nothing
      ExprBinary operator left right <- pure assignment.assignmentValue.value | _ => Nothing
      ExprName xRead <- pure left.value | _ => Nothing
      ExprName yRead <- pure right.value | _ => Nothing
      scope <- scopeFor resolved fn.functionBody
      reads <- usesInScope resolved scope.id [(x, left), (y, right)]
      pure (reads && symbolId target == symbolId x && assignment.assignmentOperator.value == AssignValue &&
            operator.value == BinaryAdd && nodeHasScope resolved scope.id assignment.assignmentValue &&
            nodeHasScope resolved scope.id assignment.assignmentTarget &&
            nodeHasScope resolved scope.id target &&
            referenceInventory resolved
              [(DeclarationReference, fnInfo.nodeId, fn.functionName),
               (DeclarationReference, xp.astInfo.nodeId, x),
               (DeclarationReference, yp.astInfo.nodeId, y),
               (AssignmentTarget, assignment.assignmentTarget.astInfo.nodeId, target),
               (ValueReference, left.astInfo.nodeId, xRead),
               (ValueReference, right.astInfo.nodeId, yRead)])) `shouldBe` Right True

  test "nested signature and local types have scopes on every visited type node" $
    checkSource "const n: i32 = 2; fn f(value: &([i32; n], &[i32])) -> [i32; n] { let local: [i32; n] = [0; n]; }" (\resolved => do
      (_, con) <- constantNamed "n" resolved
      (_, fn) <- functionNamed "f" resolved
      [parameter] <- pure fn.functionParameters | _ => Nothing
      NormalParameter _ _ _ referenceType <- pure parameter.value | _ => Nothing
      TyReference _ tupleType <- pure referenceType.value | _ => Nothing
      TyTuple (arrayType ::: [sliceReference]) <- pure tupleType.value | _ => Nothing
      TyArray elementType parameterSize <- pure arrayType.value | _ => Nothing
      TyReference _ sliceType <- pure sliceReference.value | _ => Nothing
      TySlice sliceElement <- pure sliceType.value | _ => Nothing
      returnType <- fn.returnType
      TyArray returnElement returnSize <- pure returnType.value | _ => Nothing
      local <- letAt 0 fn.functionBody
      localType <- local.letTypeAnnotation
      TyArray localElement localSize <- pure localType.value | _ => Nothing
      init <- initializer local
      ExprRepeatedArray zero count <- pure init.value | _ => Nothing
      functionScope <- scopeFor resolved parameter
      bodyScope <- scopeFor resolved fn.functionBody
      signatureUses <- usesInScope resolved functionScope.id [(con.constName, parameterSize), (con.constName, returnSize)]
      bodyUses <- usesInScope resolved bodyScope.id [(con.constName, localSize), (con.constName, count)]
      pure (signatureUses && bodyUses && functionScope.id /= bodyScope.id &&
            all (nodeHasScope resolved functionScope.id)
              [referenceType, tupleType, arrayType, elementType, sliceReference, sliceType, sliceElement, returnType, returnElement] &&
            all (nodeHasScope resolved bodyScope.id) [localType, localElement] &&
            all (nodeHasScope resolved bodyScope.id) [init, zero] &&
            nodeHasScope resolved resolved.rootScope con.constType)) `shouldBe` Right True

  test "cast target type nodes have the enclosing expression scope" $
    checkSource "fn f(a: [i32; 2], n: i32) { a as [i32; n]; }" (\resolved => do
      (_, fn) <- functionNamed "f" resolved
      expression <- exprAt 0 fn.functionBody
      ExprCast _ target <- pure expression.value | _ => Nothing
      TyArray element _ <- pure target.value | _ => Nothing
      scope <- scopeFor resolved fn.functionBody
      pure (nodeHasScope resolved scope.id expression &&
            all (nodeHasScope resolved scope.id) [target, element])) `shouldBe` Right True

  test "nested pattern containers and wildcards have scopes but introduce only named binders" $
    checkSource "fn f() { let (a, [_, b]) = (1, [2, 3]); }" (\resolved => do
      (_, fn) <- functionNamed "f" resolved
      binding <- letAt 0 fn.functionBody
      PatternTuple (aPattern ::: [arrayPattern]) <- pure binding.letPattern.value | _ => Nothing
      PatternArray [wildcard, bPattern] <- pure arrayPattern.value | _ => Nothing
      PatternWildcard <- pure wildcard.value | _ => Nothing
      a <- binder aPattern
      b <- binder bPattern
      scope <- scopeFor resolved fn.functionBody
      init <- initializer binding
      ExprTuple (one ::: [arrayExpression]) <- pure init.value | _ => Nothing
      ExprArray [two, three] <- pure arrayExpression.value | _ => Nothing
      pure (all (nodeHasScope resolved scope.id) [binding.letPattern, aPattern, arrayPattern, wildcard, bPattern] &&
            all (nodeHasScope resolved scope.id) [init, one, arrayExpression, two, three] &&
            (scope.declaredSymbolsInOrder <>> []) == [symbolId a, symbolId b] &&
            sort (map fst (SortedMap.toList resolved.tables.localVariables)) == sort [symbolId a, symbolId b] &&
            sort (map (.declaredName) (sourceSymbols resolved)) == ["", "a", "b", "f"] &&
            length (allReferences resolved) == 3 &&
            all (\ref => not (elem ref.occurrence.nodeId
                 [binding.letPattern.astInfo.nodeId, arrayPattern.astInfo.nodeId, wildcard.astInfo.nodeId]))
              (allReferences resolved))) `shouldBe` Right True

  test "small shadowing fixtures have exact symbol, binding, declaration and reference inventories" $
    checkSource "const n: i32 = 1; fn f(x: i32) { let y = x; let y = y; y; }" (\resolved => do
      (constInfo, con) <- constantNamed "n" resolved
      (fnInfo, fn) <- functionNamed "f" resolved
      [parameter] <- pure fn.functionParameters | _ => Nothing
      [x] <- parameterNames fn | _ => Nothing
      first <- letAt 0 fn.functionBody
      second <- letAt 1 fn.functionBody
      y1 <- binder first.letPattern
      y2 <- binder second.letPattern
      xUseExpr <- initializer first
      y1UseExpr <- initializer second
      y2UseExpr <- exprAt 2 fn.functionBody
      ExprName xUse <- pure xUseExpr.value | _ => Nothing
      ExprName y1Use <- pure y1UseExpr.value | _ => Nothing
      ExprName y2Use <- pure y2UseExpr.value | _ => Nothing
      root <- lookup resolved.rootScope resolved.tables.scopes
      functionScope <- scopeFor resolved parameter
      bodyScope <- scopeFor resolved fn.functionBody
      orderedRoot <- traverse (\id => lookup id resolved.tables.symbols) (root.declaredSymbolsInOrder <>> [])
      pure (sort (map (.symbolId) (sourceSymbols resolved)) ==
              sort [resolved.rootModule, symbolId con.constName, symbolId fn.functionName, symbolId x, symbolId y1, symbolId y2] &&
            sort (map fst (SortedMap.toList resolved.tables.localVariables)) == sort [symbolId x, symbolId y1, symbolId y2] &&
            map (.declaredName) orderedRoot == ["<prelude>", "n", "f"] &&
            map (\(name, binding) => (name, binding.target)) (SortedMap.toList root.valueBindings) ==
              [("f", symbolId fn.functionName), ("n", symbolId con.constName)] &&
            map (\(name, binding) => (name, binding.target)) (SortedMap.toList functionScope.valueBindings) == [("x", symbolId x)] &&
            map (\(name, binding) => (name, binding.target)) (SortedMap.toList bodyScope.valueBindings) == [("y", symbolId y2)] &&
            (functionScope.declaredSymbolsInOrder <>> []) == [symbolId x] &&
            (bodyScope.declaredSymbolsInOrder <>> []) == [symbolId y1, symbolId y2] &&
            symbolId xUse == symbolId x && symbolId y1Use == symbolId y1 && symbolId y2Use == symbolId y2 &&
            referenceInventory resolved
              [(DeclarationReference, constInfo.nodeId, con.constName),
               (DeclarationReference, fnInfo.nodeId, fn.functionName),
               (DeclarationReference, parameter.astInfo.nodeId, x),
               (DeclarationReference, first.letPattern.astInfo.nodeId, y1),
               (ValueReference, xUseExpr.astInfo.nodeId, xUse),
               (DeclarationReference, second.letPattern.astInfo.nodeId, y2),
               (ValueReference, y1UseExpr.astInfo.nodeId, y1Use),
               (ValueReference, y2UseExpr.astInfo.nodeId, y2Use)])) `shouldBe` Right True

  test "constant initializers can reference later constants with module scope and identity" $
    checkSource "const first: i32 = later; const later: i32 = 2; fn f() { first; later; }" (\resolved => do
      (firstInfo, first) <- constantNamed "first" resolved
      (laterInfo, later) <- constantNamed "later" resolved
      (fnInfo, fn) <- functionNamed "f" resolved
      ExprName forward <- pure first.constValue.value | _ => Nothing
      firstUse <- exprAt 0 fn.functionBody
      laterUse <- exprAt 1 fn.functionBody
      body <- scopeFor resolved fn.functionBody
      forwardOK <- usesInScope resolved resolved.rootScope [(later.constName, first.constValue)]
      bodyOK <- usesInScope resolved body.id [(first.constName, firstUse), (later.constName, laterUse)]
      pure (forwardOK && bodyOK && symbolId first.constName /= symbolId later.constName &&
            referenceMatches resolved DeclarationReference firstInfo.nodeId first.constName &&
            referenceMatches resolved DeclarationReference laterInfo.nodeId later.constName &&
            length (allReferences resolved) == 6)) `shouldBe` Right True

  test "duplicate constants identify the original symbol and both declaration spans" $
    duplicateDeclaration "const n: i32 = 1;" "const n: i32 = 2;" "n" (2, 7, 2, 8) `shouldBe` Right True

  test "a constant conflicting with an earlier function reports that function" $
    duplicateDeclaration "fn f() {}" "const f: i32 = 1;" "f" (2, 7, 2, 8) `shouldBe` Right True

  test "a let binder cannot shadow a module constant" $
    constantShadowing "const N: i32 = 1;\nfn f() { let N = 2; }"
      `shouldBe` Right ("N", (2, 14, 2, 15), (1, 7, 1, 8))

  test "a mutable let binder cannot shadow a module constant" $
    constantShadowing "const N: i32 = 1;\nfn f() { let mut N = 2; }"
      `shouldBe` Right ("N", (2, 18, 2, 19), (1, 7, 1, 8))

  test "a binder nested in a destructuring pattern cannot shadow a constant" $
    constantShadowing "const N: i32 = 1;\nfn f() { let (a, N) = (1, 2); }"
      `shouldBe` Right ("N", (2, 18, 2, 19), (1, 7, 1, 8))

  test "a let binder in a nested block cannot shadow a module constant" $
    constantShadowing "const N: i32 = 1;\nfn f() { { let N = 2; } }"
      `shouldBe` Right ("N", (2, 16, 2, 17), (1, 7, 1, 8))

  test "a function parameter cannot shadow a module constant" $
    constantShadowing "const N: i32 = 1;\nfn f(N: i32) {}"
      `shouldBe` Right ("N", (2, 6, 2, 7), (1, 7, 1, 8))

  test "a for binder cannot shadow a module constant" $
    constantShadowing "const N: i32 = 1;\nfn f() { for N in [1] {} }"
      `shouldBe` Right ("N", (2, 14, 2, 15), (1, 7, 1, 8))

  test "a binder cannot shadow a constant declared later in the module" $
    constantShadowing "fn f() { let N = 2; }\nconst N: i32 = 1;"
      `shouldBe` Right ("N", (1, 14, 1, 15), (2, 7, 2, 8))

  test "a binder cannot shadow a constant that itself shadows a prelude function" $
    constantShadowing "const sin: i32 = 1;\nfn f() { let sin = 2; }"
      `shouldBe` Right ("sin", (2, 14, 2, 17), (1, 7, 1, 10))

  test "constant-shadowing diagnostics identify the constant's symbol" $
    (do expected <- checkSource "const N: i32 = 1;" (\resolved =>
          map (\(_, con) => symbolId con.constName) (constantNamed "N" resolved))
        case resolveSource "const N: i32 = 1;\nfn f() { let N = 2; }" of
          Left (ResolutionFailure (BindingShadowsConstant _ actual _ _)) => Right (actual == expected)
          Left err => Left (show err)
          Right _ => Left "Expected BindingShadowsConstant, but resolution succeeded") `shouldBe` Right True

  test "parameters and locals may still shadow module functions" $
    checkSource "fn g() {} fn f(g: i32) { let g = g; g; }" (\resolved => do
      (_, f) <- functionNamed "f" resolved
      [parameter] <- parameterNames f | _ => Nothing
      binding <- letAt 0 f.functionBody
      local <- binder binding.letPattern
      init <- initializer binding
      final <- exprAt 1 f.functionBody
      initUsesParameter <- useMatches resolved parameter init
      finalUsesLocal <- useMatches resolved local final
      pure (initUsesParameter && finalUsesLocal)) `shouldBe` Right True
