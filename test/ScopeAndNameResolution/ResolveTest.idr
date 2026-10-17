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
  -- Rendered from real resolution, so the spans are the ones the resolver recorded.
  -- InaccessibleSymbol is not covered: visibility is not checked yet.
  test "resolution diagnostics report the recorded source positions" $
    map (\source => either show (const "resolved") (resolveSource source))
      [ "fn f() {}\nfn f() {}"
      , "const N: i32 = 1;\nfn f() { let mut N = 2; }"
      , "fn f(n: i32) {\n  [0; n];\n}"
      ] `shouldBe`
      [ "Resolution: duplicate f at 2:4; previous declaration at 1:4"
      , "Resolution: binding N at 2:18 shadows the constant at 1:7"
      , "Resolution: non-constant n at 2:7 declared at 1:6"
      ]

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

  test "a declaration without an initializer has one mutable local and exact read/write references" $
    checkSource "fn f() { let mut x: i32; x = 1; x; }" (\resolved => do
      (fnInfo, fn) <- functionNamed "f" resolved
      binding <- letAt 0 fn.functionBody
      x <- binder binding.letPattern
      annotation <- binding.letTypeAnnotation
      assignment <- assignmentAt 1 fn.functionBody
      AssignTargetName target <- pure assignment.assignmentTarget.value | _ => Nothing
      final <- exprAt 2 fn.functionBody
      ExprName read <- pure final.value | _ => Nothing
      scope <- scopeFor resolved fn.functionBody
      readOK <- usesInScope resolved scope.id [(x, final)]
      pure (isNothing binding.letInitializer && symbolId target == symbolId x && readOK &&
            nodeHasScope resolved scope.id annotation &&
            nodeHasScope resolved scope.id assignment.assignmentTarget &&
            nodeHasScope resolved scope.id assignment.assignmentValue &&
            bindingMatches scope x && localMatches resolved x True &&
            symbolMatches resolved x scope.id "local" x.astInfo &&
            (scope.declaredSymbolsInOrder <>> []) == [symbolId x] &&
            map fst (SortedMap.toList resolved.tables.localVariables) == [symbolId x] &&
            referenceInventory resolved
              [(DeclarationReference, fnInfo.nodeId, fn.functionName),
               (DeclarationReference, binding.letPattern.astInfo.nodeId, x),
               (AssignmentTarget, assignment.assignmentTarget.astInfo.nodeId, target),
               (ValueReference, final.astInfo.nodeId, read)])) `shouldBe` Right True

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

  test "destructuring initializers use both old parameters before introducing shadowing locals" $
    checkSource "fn f(x: i32, y: i32) { let (x, y) = (y, x); x; y; }" (\resolved => do
      (fnInfo, fn) <- functionNamed "f" resolved
      [xp, yp] <- pure fn.functionParameters | _ => Nothing
      [x, y] <- parameterNames fn | _ => Nothing
      binding <- letAt 0 fn.functionBody
      [(xPattern, newX), (yPattern, newY)] <- pure (patternBinders binding.letPattern) | _ => Nothing
      init <- initializer binding
      ExprTuple (oldYUse ::: [oldXUse]) <- pure init.value | _ => Nothing
      ExprName oldY <- pure oldYUse.value | _ => Nothing
      ExprName oldX <- pure oldXUse.value | _ => Nothing
      finalX <- exprAt 1 fn.functionBody
      finalY <- exprAt 2 fn.functionBody
      ExprName readX <- pure finalX.value | _ => Nothing
      ExprName readY <- pure finalY.value | _ => Nothing
      functionScope <- scopeFor resolved xp
      bodyScope <- scopeFor resolved fn.functionBody
      usesOK <- usesInScope resolved bodyScope.id [(y, oldYUse), (x, oldXUse), (newX, finalX), (newY, finalY)]
      pure (usesOK && length (nub (map symbolId [x, y, newX, newY])) == 4 &&
            bodyScope.parent == Just functionScope.id &&
            all (bindingMatches functionScope) [x, y] && all (bindingMatches bodyScope) [newX, newY] &&
            all (\name => localMatches resolved name False) [x, y, newX, newY] &&
            (functionScope.declaredSymbolsInOrder <>> []) == map symbolId [x, y] &&
            (bodyScope.declaredSymbolsInOrder <>> []) == map symbolId [newX, newY] &&
            referenceInventory resolved
              [(DeclarationReference, fnInfo.nodeId, fn.functionName),
               (DeclarationReference, xp.astInfo.nodeId, x),
               (DeclarationReference, yp.astInfo.nodeId, y),
               (DeclarationReference, xPattern.astInfo.nodeId, newX),
               (DeclarationReference, yPattern.astInfo.nodeId, newY),
               (ValueReference, oldYUse.astInfo.nodeId, oldY),
               (ValueReference, oldXUse.astInfo.nodeId, oldX),
               (ValueReference, finalX.astInfo.nodeId, readX),
               (ValueReference, finalY.astInfo.nodeId, readY)])) `shouldBe` Right True

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
            (case loopScope.origin of SourceScope info => info.nodeId == loop.astInfo.nodeId; _ => False) &&
            (case bodyScope.origin of SourceScope info => info.nodeId == body.astInfo.nodeId; _ => False) &&
            bindingMatches outer outerName && bindingMatches loopScope loopName &&
            lookup loop.astInfo.nodeId resolved.tables.nodeScopes == Just outer.id &&
            referenceMatches resolved DeclarationReference pattern.astInfo.nodeId loopName &&
            localMatches resolved loopName False)) `shouldBe` Right True

  test "nested for loops restore each shadowed binding and keep their iterator scopes separate" $
    checkSource "fn f(i: i32) { for i in [i] { for i in [i] { i; } i; } i; }" (\resolved => do
      (fnInfo, fn) <- functionNamed "f" resolved
      [parameter] <- pure fn.functionParameters | _ => Nothing
      [original] <- parameterNames fn | _ => Nothing
      outerLoop <- exprAt 0 fn.functionBody
      ExprFor outerPattern outerIterator outerBody <- pure outerLoop.value | _ => Nothing
      ExprArray [originalIteratorUse] <- pure outerIterator.value | _ => Nothing
      outer <- binder outerPattern
      innerLoop <- exprAt 0 outerBody
      ExprFor innerPattern innerIterator innerBody <- pure innerLoop.value | _ => Nothing
      ExprArray [outerIteratorUse] <- pure innerIterator.value | _ => Nothing
      inner <- binder innerPattern
      innerUse <- exprAt 0 innerBody
      afterInner <- exprAt 1 outerBody
      afterOuter <- exprAt 1 fn.functionBody
      ExprName originalIteratorName <- pure originalIteratorUse.value | _ => Nothing
      ExprName outerIteratorName <- pure outerIteratorUse.value | _ => Nothing
      ExprName innerRead <- pure innerUse.value | _ => Nothing
      ExprName outerRead <- pure afterInner.value | _ => Nothing
      ExprName originalRead <- pure afterOuter.value | _ => Nothing
      functionScope <- scopeFor resolved parameter
      bodyScope <- scopeFor resolved fn.functionBody
      outerScope <- scopeFor resolved outerPattern
      outerBodyScope <- scopeFor resolved outerBody
      innerScope <- scopeFor resolved innerPattern
      innerBodyScope <- scopeFor resolved innerBody
      originalUsesOK <- usesInScope resolved bodyScope.id [(original, originalIteratorUse), (original, afterOuter)]
      outerUsesOK <- usesInScope resolved outerBodyScope.id [(outer, outerIteratorUse), (outer, afterInner)]
      innerUseOK <- usesInScope resolved innerBodyScope.id [(inner, innerUse)]
      pure (originalUsesOK && outerUsesOK && innerUseOK &&
            length (nub (map symbolId [original, outer, inner])) == 3 &&
            (case (outerScope.kind, innerScope.kind) of (ForScope, ForScope) => True; _ => False) &&
            outerScope.parent == Just bodyScope.id && outerBodyScope.parent == Just outerScope.id &&
            innerScope.parent == Just outerBodyScope.id && innerBodyScope.parent == Just innerScope.id &&
            isBlock outerBodyScope && isBlock innerBodyScope &&
            all (nodeHasScope resolved bodyScope.id) [outerLoop, outerIterator] &&
            all (nodeHasScope resolved outerBodyScope.id) [innerLoop, innerIterator] &&
            bindingMatches functionScope original && bindingMatches outerScope outer && bindingMatches innerScope inner &&
            all (\name => localMatches resolved name False) [original, outer, inner] &&
            (functionScope.declaredSymbolsInOrder <>> []) == [symbolId original] &&
            (outerScope.declaredSymbolsInOrder <>> []) == [symbolId outer] &&
            (innerScope.declaredSymbolsInOrder <>> []) == [symbolId inner] &&
            referenceInventory resolved
              [(DeclarationReference, fnInfo.nodeId, fn.functionName),
               (DeclarationReference, parameter.astInfo.nodeId, original),
               (DeclarationReference, outerPattern.astInfo.nodeId, outer),
               (DeclarationReference, innerPattern.astInfo.nodeId, inner),
               (ValueReference, originalIteratorUse.astInfo.nodeId, originalIteratorName),
               (ValueReference, outerIteratorUse.astInfo.nodeId, outerIteratorName),
               (ValueReference, innerUse.astInfo.nodeId, innerRead),
               (ValueReference, afterInner.astInfo.nodeId, outerRead),
               (ValueReference, afterOuter.astInfo.nodeId, originalRead)])) `shouldBe` Right True

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

  test "controlled blocks resolve every operand before entering the child scope" $
    checkSource "fn f(q: qubit, r: qubit) { ctrl(&q, &r) { let q = 1; q; r; } q; r; }" (\resolved => do
      (fnInfo, fn) <- functionNamed "f" resolved
      [qParameter, rParameter] <- pure fn.functionParameters | _ => Nothing
      [q, r] <- parameterNames fn | _ => Nothing
      controlled <- exprAt 0 fn.functionBody
      ExprCtrl (ControlledBlock (firstControl ::: [secondControl]) _ block) <- pure controlled.value
        | _ => Nothing
      ExprUnary _ firstOperand <- pure firstControl.value | _ => Nothing
      ExprUnary _ secondOperand <- pure secondControl.value | _ => Nothing
      innerBinding <- letAt 0 block
      innerQ <- binder innerBinding.letPattern
      innerQUse <- exprAt 1 block
      innerRUse <- exprAt 2 block
      afterQ <- exprAt 1 fn.functionBody
      afterR <- exprAt 2 fn.functionBody
      outer <- scopeFor resolved fn.functionBody
      inner <- scopeFor resolved block
      outerUses <- usesInScope resolved outer.id
        [(q, firstOperand), (r, secondOperand), (q, afterQ), (r, afterR)]
      innerUses <- usesInScope resolved inner.id [(innerQ, innerQUse), (r, innerRUse)]
      valueOccurrences <- traverse valueReferenceOccurrence
        [firstOperand, secondOperand, innerQUse, innerRUse, afterQ, afterR]
      pure (outerUses && innerUses && length (nub (map symbolId [q, r, innerQ])) == 3 &&
            all (nodeHasScope resolved outer.id) [controlled, firstControl, secondControl] &&
            inner.id /= outer.id && inner.parent == Just outer.id && isBlock inner &&
            bindingMatches inner innerQ && localMatches resolved innerQ False &&
            symbolMatches resolved innerQ inner.id "local" innerQ.astInfo &&
            (inner.declaredSymbolsInOrder <>> []) == [symbolId innerQ] &&
            isNothing (lookup "q" outer.valueBindings) && isNothing (lookup "r" inner.valueBindings) &&
            referenceInventory resolved
              ([(DeclarationReference, fnInfo.nodeId, fn.functionName),
                (DeclarationReference, qParameter.astInfo.nodeId, q),
                (DeclarationReference, rParameter.astInfo.nodeId, r),
                (DeclarationReference, innerBinding.letPattern.astInfo.nodeId, innerQ)] ++
               valueOccurrences))) `shouldBe` Right True

  test "controlled callables resolve every control and the callable in the enclosing scope" $
    checkSource "unitary fn g(target: &qubit) {} unitary fn f(q: &qubit, r: &qubit) { ctrl(q, r).apply(g); }" (\resolved => do
      (gInfo, g) <- functionNamed "g" resolved
      (fInfo, f) <- functionNamed "f" resolved
      [targetParameter] <- pure g.functionParameters | _ => Nothing
      [target] <- parameterNames g | _ => Nothing
      [qParameter, rParameter] <- pure f.functionParameters | _ => Nothing
      [q, r] <- parameterNames f | _ => Nothing
      controlled <- exprAt 0 f.functionBody
      ExprCtrl (ControlledCallable (firstControl ::: [secondControl]) _ callable) <- pure controlled.value
        | _ => Nothing
      body <- scopeFor resolved f.functionBody
      reads <- usesInScope resolved body.id [(q, firstControl), (r, secondControl), (g.functionName, callable)]
      valueOccurrences <- traverse valueReferenceOccurrence [firstControl, secondControl, callable]
      pure (reads && symbolId q /= symbolId r && nodeHasScope resolved body.id controlled &&
            (body.declaredSymbolsInOrder <>> []) == [] &&
            referenceInventory resolved
              ([(DeclarationReference, gInfo.nodeId, g.functionName),
                (DeclarationReference, targetParameter.astInfo.nodeId, target),
                (DeclarationReference, fInfo.nodeId, f.functionName),
                (DeclarationReference, qParameter.astInfo.nodeId, q),
                (DeclarationReference, rParameter.astInfo.nodeId, r)] ++
               valueOccurrences))) `shouldBe` Right True

  test "controlled blocks reject an unresolved second control operand" $
    unresolved "fn f(q: qubit) { ctrl(&q, &missing) {} }" "missing" `shouldBe` Right True

  test "controlled callables reject an unresolved second control operand" $
    unresolved "unitary fn g(target: &qubit) {} unitary fn f(q: &qubit) { ctrl(q, missing).apply(g); }" "missing" `shouldBe` Right True

  test "parameter and return annotations see module functions" $
    checkSource "const fn n() -> i32 { 2 } fn f(m: i32, values: [i32; n()]) -> [i32; n()] { values }" (\resolved => do
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
  test "a local from an earlier function is unavailable in a later function" $
    unresolved "fn f() { let x = 1; } fn g() { x; }" "x" `shouldBe` Right True
  test "a local in a later function is unavailable in an earlier function" $
    unresolved "fn f() { x; } fn g() { let x = 1; }" "x" `shouldBe` Right True
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
    expressionUses "[x; N]" ["x", "N"] (\expression => case expression.value of
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
    expressionUses "a as [i32; N]" ["a", "N"] (\expression => do
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

  test "compound assignment preserves its operator and resolves each written name once" $
    checkSource "fn f(mut x: i32, y: i32) { x += y; }" (\resolved => do
      (fnInfo, fn) <- functionNamed "f" resolved
      [xp, yp] <- pure fn.functionParameters | _ => Nothing
      [x, y] <- parameterNames fn | _ => Nothing
      assignment <- assignmentAt 0 fn.functionBody
      AssignTargetName target <- pure assignment.assignmentTarget.value | _ => Nothing
      ExprName yRead <- pure assignment.assignmentValue.value | _ => Nothing
      scope <- scopeFor resolved fn.functionBody
      reads <- usesInScope resolved scope.id [(y, assignment.assignmentValue)]
      pure (reads && symbolId target == symbolId x && assignment.assignmentOperator.value == AssignAdd &&
            nodeHasScope resolved scope.id assignment.assignmentValue &&
            nodeHasScope resolved scope.id assignment.assignmentTarget &&
            nodeHasScope resolved scope.id target &&
            referenceInventory resolved
              [(DeclarationReference, fnInfo.nodeId, fn.functionName),
               (DeclarationReference, xp.astInfo.nodeId, x),
               (DeclarationReference, yp.astInfo.nodeId, y),
               (AssignmentTarget, assignment.assignmentTarget.astInfo.nodeId, target),
               (ValueReference, assignment.assignmentValue.astInfo.nodeId, yRead)])) `shouldBe` Right True

  test "a compound index block has one scope and its local does not escape" $
    checkSource "fn f(mut a: [i32; 2], i: i32) { a[{ let i = 0; i }] += 1; i; }" (\resolved => do
      (fnInfo, fn) <- functionNamed "f" resolved
      [ap, ip] <- pure fn.functionParameters | _ => Nothing
      [a, i] <- parameterNames fn | _ => Nothing
      assignment <- assignmentAt 0 fn.functionBody
      AssignTargetIndex object index <- pure assignment.assignmentTarget.value | _ => Nothing
      ExprName aRead <- pure object.value | _ => Nothing
      block <- blockBody index
      localBinding <- letAt 0 block
      local <- binder localBinding.letPattern
      final <- block.value.finalExpression
      ExprName localRead <- pure final.value | _ => Nothing
      after <- exprAt 1 fn.functionBody
      ExprName outerRead <- pure after.value | _ => Nothing
      bodyScope <- scopeFor resolved fn.functionBody
      indexScope <- scopeFor resolved block
      objectOK <- useMatches resolved a object
      localOK <- useMatches resolved local final
      afterOK <- useMatches resolved i after
      pure (assignment.assignmentOperator.value == AssignAdd &&
            objectOK && localOK && afterOK && symbolId local /= symbolId i &&
            indexScope.parent == Just bodyScope.id &&
            blockScopesMatchNodes resolved && bindingMatches indexScope local &&
            localMatches resolved local False &&
            (indexScope.declaredSymbolsInOrder <>> []) == [symbolId local] &&
            referenceInventory resolved
              [(DeclarationReference, fnInfo.nodeId, fn.functionName),
               (DeclarationReference, ap.astInfo.nodeId, a),
               (DeclarationReference, ip.astInfo.nodeId, i),
               (ValueReference, object.astInfo.nodeId, aRead),
               (DeclarationReference, localBinding.letPattern.astInfo.nodeId, local),
               (ValueReference, final.astInfo.nodeId, localRead),
               (ValueReference, after.astInfo.nodeId, outerRead)])) `shouldBe` Right True

  test "a compound index block without references still has exactly one scope" $
    checkSource "fn f(mut a: [i32; 2]) { a[{ 0 }] += 1; }" (\resolved => do
      (_, fn) <- functionNamed "f" resolved
      assignment <- assignmentAt 0 fn.functionBody
      AssignTargetIndex _ index <- pure assignment.assignmentTarget.value | _ => Nothing
      block <- blockBody index
      indexScope <- scopeFor resolved block
      pure (blockScopesMatchNodes resolved && isBlock indexScope &&
            null (indexScope.declaredSymbolsInOrder <>> []) &&
            length (filter (isBlock . snd) (SortedMap.toList resolved.tables.scopes)) == 2))
      `shouldBe` Right True

  test "nested compound targets retain consistent block scopes" $
    checkSource "fn f(mut a: [i32; 2]) { a[{ let i = 0; let mut b = [0]; b[{ i }] += 1; i }] += 1; }"
      (\resolved => Just (blockScopesMatchNodes resolved &&
        length (filter (isBlock . snd) (SortedMap.toList resolved.tables.scopes)) == 3))
      `shouldBe` Right True

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
    checkSource "const N: i32 = 2; fn f(a: [i32; 2]) { a as [i32; N]; }" (\resolved => do
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

  test "an immutable bare constant pattern reuses the constant without creating a local" $
    checkSource "const U: () = (); fn f() { let U = (); U; }" (\resolved => do
      (_, con) <- constantNamed "U" resolved
      (_, fn) <- functionNamed "f" resolved
      binding <- letAt 0 fn.functionBody
      final <- exprAt 1 fn.functionBody
      useOK <- useMatches resolved con.constName final
      pure (constantPatternMatches resolved con.constName binding.letPattern && useOK &&
            null (SortedMap.toList resolved.tables.localVariables))) `shouldBe` Right True

  test "a mutable let binder cannot shadow a module constant" $
    constantShadowing "const N: i32 = 1;\nfn f() { let mut N = 2; }"
      `shouldBe` Right ("N", (2, 18, 2, 19), (1, 7, 1, 8))

  test "a tuple can contain a local binder and repeated constant patterns" $
    checkSource "const U: () = (); fn f() { let (x, U, U) = (1, (), ()); x; }" (\resolved => do
      (_, con) <- constantNamed "U" resolved
      (_, fn) <- functionNamed "f" resolved
      binding <- letAt 0 fn.functionBody
      PatternTuple patterns <- pure binding.letPattern.value | _ => Nothing
      [xPattern, first, second] <- pure (forget patterns) | _ => Nothing
      x <- binder xPattern
      final <- exprAt 1 fn.functionBody
      useOK <- useMatches resolved x final
      scope <- scopeFor resolved binding.letPattern
      pure (constantPatternMatches resolved con.constName first &&
            constantPatternMatches resolved con.constName second &&
            localMatches resolved x False && bindingMatches scope x && useOK &&
            (scope.declaredSymbolsInOrder <>> []) == [symbolId x] &&
            length (SortedMap.toList resolved.tables.localVariables) == 1)) `shouldBe` Right True

  test "an array can contain repeated constant patterns without introducing bindings" $
    checkSource "const U: () = (); fn f() { let [U, U] = [(), ()]; }" (\resolved => do
      (_, con) <- constantNamed "U" resolved
      (_, fn) <- functionNamed "f" resolved
      binding <- letAt 0 fn.functionBody
      PatternArray [first, second] <- pure binding.letPattern.value | _ => Nothing
      pure (constantPatternMatches resolved con.constName first &&
            constantPatternMatches resolved con.constName second &&
            null (SortedMap.toList resolved.tables.localVariables))) `shouldBe` Right True

  test "constant patterns remain references in nested blocks" $
    checkSource "const U: () = (); fn f() { { let U = (); } }" (\resolved => do
      (_, con) <- constantNamed "U" resolved
      (_, fn) <- functionNamed "f" resolved
      inner <- exprAt 0 fn.functionBody >>= blockBody
      binding <- letAt 0 inner
      pure (constantPatternMatches resolved con.constName binding.letPattern &&
            null (SortedMap.toList resolved.tables.localVariables))) `shouldBe` Right True

  test "repeated constant parameters are pattern references and introduce no parameters" $
    checkSource "const U: () = (); fn f(U: (), U: ()) { U; }" (\resolved => do
      (_, con) <- constantNamed "U" resolved
      (_, fn) <- functionNamed "f" resolved
      [first, second] <- pure fn.functionParameters | _ => Nothing
      [firstName, secondName] <- parameterNames fn | _ => Nothing
      use <- exprAt 0 fn.functionBody
      useOK <- useMatches resolved con.constName use
      pure (constantOccurrenceMatches resolved con.constName first.astInfo.nodeId firstName &&
            constantOccurrenceMatches resolved con.constName second.astInfo.nodeId secondName && useOK &&
            null (SortedMap.toList resolved.tables.localVariables))) `shouldBe` Right True

  test "for constant patterns introduce no loop binding" $
    checkSource "const U: () = (); fn f() { for U in [()] { U; } }" (\resolved => do
      (_, con) <- constantNamed "U" resolved
      (_, fn) <- functionNamed "f" resolved
      loop <- exprAt 0 fn.functionBody
      ExprFor pattern _ body <- pure loop.value | _ => Nothing
      use <- exprAt 0 body
      useOK <- useMatches resolved con.constName use
      pure (constantPatternMatches resolved con.constName pattern && useOK &&
            null (SortedMap.toList resolved.tables.localVariables))) `shouldBe` Right True

  test "repeated constant tuple patterns introduce no for-loop bindings" $
    checkForPattern "const U: () = (); fn f() { let (U, U) = ((), ()); for unused in [((), ())] { U; } }" (\resolved => do
      (_, con) <- constantNamed "U" resolved
      (_, fn) <- functionNamed "f" resolved
      loop <- exprAt 0 fn.functionBody
      ExprFor pattern _ body <- pure loop.value | _ => Nothing
      PatternTuple patterns <- pure pattern.value | _ => Nothing
      [first, second] <- pure (forget patterns) | _ => Nothing
      loopScope <- scopeFor resolved pattern
      use <- exprAt 0 body
      useOK <- useMatches resolved con.constName use
      pure (constantPatternMatches resolved con.constName first &&
            constantPatternMatches resolved con.constName second && useOK &&
            (case loopScope.kind of ForScope => True; _ => False) &&
            null (SortedMap.toList loopScope.valueBindings) &&
            null (SortedMap.toList resolved.tables.localVariables))) `shouldBe` Right True

  test "a constant declared later in the module is still a constant pattern" $
    checkSource "fn f() { let U = (); } const U: () = ();" (\resolved => do
      (_, con) <- constantNamed "U" resolved
      (_, fn) <- functionNamed "f" resolved
      binding <- letAt 0 fn.functionBody
      pure (constantPatternMatches resolved con.constName binding.letPattern &&
            null (SortedMap.toList resolved.tables.localVariables))) `shouldBe` Right True

  test "a constant shadowing a prelude function is interpreted as a pattern" $
    checkSource "const sin: () = (); fn f() { let sin = (); }" (\resolved => do
      (_, con) <- constantNamed "sin" resolved
      (_, fn) <- functionNamed "f" resolved
      binding <- letAt 0 fn.functionBody
      pure (constantPatternMatches resolved con.constName binding.letPattern &&
            null (SortedMap.toList resolved.tables.localVariables))) `shouldBe` Right True

  -- Resolving a constant pattern does not decide whether it is irrefutable.
  test "integer constant patterns defer refutability checking" $
    checkSource "const N: i32 = 1; fn f() { let N = 2; }" (\resolved => do
      (_, con) <- constantNamed "N" resolved
      (_, fn) <- functionNamed "f" resolved
      binding <- letAt 0 fn.functionBody
      pure (constantPatternMatches resolved con.constName binding.letPattern)) `shouldBe` Right True

  test "a mutable binder nested in a destructuring pattern cannot shadow a constant" $
    constantShadowing "const N: i32 = 1;\nfn f() { let (a, mut N) = (1, 2); }"
      `shouldBe` Right ("N", (2, 22, 2, 23), (1, 7, 1, 8))

  test "a mutable function parameter cannot shadow a constant" $
    constantShadowing "const N: i32 = 1;\nfn f(mut N: i32) {}"
      `shouldBe` Right ("N", (2, 10, 2, 11), (1, 7, 1, 8))

  test "a mutable for binder cannot shadow a constant" $
    forConstantShadowing "const N: i32 = 1;\nfn f() { let mut N = 1; for unused in [1] {} }"
      `shouldBe` Right ("N", (2, 18, 2, 19), (1, 7, 1, 8))

  test "constant-shadowing diagnostics identify the constant's symbol" $
    (do expected <- checkSource "const N: i32 = 1;" (\resolved =>
          map (\(_, con) => symbolId con.constName) (constantNamed "N" resolved))
        case resolveSource "const N: i32 = 1;\nfn f() { let mut N = 2; }" of
          Left (ResolutionFailure (BindingShadowsConstant _ actual _ _)) => Right (actual == expected)
          Left err => Left (show err)
          Right _ => Left "Expected BindingShadowsConstant, but resolution succeeded") `shouldBe` Right True

  test "a repeated tuple binder reports both occurrences" $
    duplicateBinder "fn f() { let (x, x) = (1, 2); }"
      `shouldBe` Right ("x", (1, 18, 1, 19), (1, 15, 1, 16))

  test "a repeated nested array binder reports both occurrences" $
    duplicateBinder "fn f() { let (x, [x]) = (1, [2]); }"
      `shouldBe` Right ("x", (1, 19, 1, 20), (1, 15, 1, 16))

  test "a repeated for binder reports both occurrences" $
    duplicateForBinder "fn f() { let (x, x) = (1, 2); for unused in [(1, 2)] {} }"
      `shouldBe` Right ("x", (1, 18, 1, 19), (1, 15, 1, 16))

  test "a repeated function parameter reports both occurrences" $
    duplicateBinder "fn f(x: i32, x: i32) {}"
      `shouldBe` Right ("x", (1, 14, 1, 15), (1, 6, 1, 7))

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

  test "a repeat count cannot use a parameter" $
    nonConstantUse "fn f(n: i32) { [0; n]; }"
      `shouldBe` Right ("n", (1, 20, 1, 21), (1, 6, 1, 7))

  test "an array length in a let annotation cannot use an earlier local" $
    nonConstantUse "fn f() { let n = 2; let a: [i32; n] = [0, 0]; }"
      `shouldBe` Right ("n", (1, 34, 1, 35), (1, 14, 1, 15))

  test "an array length in a cast target cannot use a parameter" $
    nonConstantUse "fn f(n: i32, a: [i32; 2]) { a as [i32; n]; }"
      `shouldBe` Right ("n", (1, 40, 1, 41), (1, 6, 1, 7))

  test "a repeat count in a nested block cannot use an enclosing local" $
    nonConstantUse "fn f() { let n = 2; { [0; n]; } }"
      `shouldBe` Right ("n", (1, 27, 1, 28), (1, 14, 1, 15))

  test "a repeat count cannot use a for binder" $
    nonConstantUse "fn f() { for i in [1] { [0; i]; } }"
      `shouldBe` Right ("i", (1, 29, 1, 30), (1, 14, 1, 15))

  test "a nested constant expression cannot use locals of its enclosing constant expression" $
    nonConstantUse "fn f() { [0; { let k = 2; [0; k]; 2 }]; }"
      `shouldBe` Right ("k", (1, 31, 1, 32), (1, 20, 1, 21))

  test "nested constant contexts restore outer constant locals and then ordinary parameter access" $
    checkSource "fn f(x: i32) { [0; { let n = 2; [0; { let m = 1; m }]; n }]; x; }" (\resolved => do
      (fnInfo, fn) <- functionNamed "f" resolved
      [parameter] <- pure fn.functionParameters | _ => Nothing
      [x] <- parameterNames fn | _ => Nothing
      repeated <- exprAt 0 fn.functionBody
      ExprRepeatedArray _ outerCount <- pure repeated.value | _ => Nothing
      outerBlock <- blockBody outerCount
      nBinding <- letAt 0 outerBlock
      n <- binder nBinding.letPattern
      innerRepeated <- exprAt 1 outerBlock
      ExprRepeatedArray _ innerCount <- pure innerRepeated.value | _ => Nothing
      innerBlock <- blockBody innerCount
      mBinding <- letAt 0 innerBlock
      m <- binder mBinding.letPattern
      mUse <- innerBlock.value.finalExpression
      nUse <- outerBlock.value.finalExpression
      xUse <- exprAt 1 fn.functionBody
      ExprName mRead <- pure mUse.value | _ => Nothing
      ExprName nRead <- pure nUse.value | _ => Nothing
      ExprName xRead <- pure xUse.value | _ => Nothing
      bodyScope <- scopeFor resolved fn.functionBody
      outerScope <- scopeFor resolved outerBlock
      innerScope <- scopeFor resolved innerBlock
      mOK <- usesInScope resolved innerScope.id [(m, mUse)]
      nOK <- usesInScope resolved outerScope.id [(n, nUse)]
      xOK <- usesInScope resolved bodyScope.id [(x, xUse)]
      pure (mOK && nOK && xOK && isNothing resolved.tables.constContextBoundary &&
            outerScope.parent == Just bodyScope.id && innerScope.parent == Just outerScope.id &&
            bindingMatches outerScope n && bindingMatches innerScope m &&
            (outerScope.declaredSymbolsInOrder <>> []) == [symbolId n] &&
            (innerScope.declaredSymbolsInOrder <>> []) == [symbolId m] &&
            referenceInventory resolved
              [(DeclarationReference, fnInfo.nodeId, fn.functionName),
               (DeclarationReference, parameter.astInfo.nodeId, x),
               (DeclarationReference, nBinding.letPattern.astInfo.nodeId, n),
               (DeclarationReference, mBinding.letPattern.astInfo.nodeId, m),
               (ValueReference, mUse.astInfo.nodeId, mRead),
               (ValueReference, nUse.astInfo.nodeId, nRead),
               (ValueReference, xUse.astInfo.nodeId, xRead)])) `shouldBe` Right True

  test "leaving a nested constant context still forbids parameters in the outer count" $
    nonConstantUse "fn f(x: i32) { [0; { [0; 2]; x }]; }"
      `shouldBe` Right ("x", (1, 30, 1, 31), (1, 6, 1, 7))

  test "constant expressions may use locals they declare themselves" $
    checkSource "fn f() { let a: [i32; { let k = 2; k }] = [0; { let m = 2; m }]; }" valueReferenceKinds
      `shouldBe` Right [("k", "local"), ("m", "local")]

  test "constant expressions may use constants, functions and prelude functions" $
    checkSource "const N: i32 = 2; const fn g() -> i32 { 2 } fn f() { [0; N]; [0; g()]; [0; abs(2)]; }" valueReferenceKinds
      `shouldBe` Right [("N", "constant"), ("g", "function"), ("abs", "function")]

  test "repeated-array elements and later uses still see locals" $
    checkSource "fn f(x: i32) { [x; 2]; let a: [i32; 2] = [x, x]; x; }" valueReferenceKinds
      `shouldBe` Right [("x", "parameter"), ("x", "parameter"), ("x", "parameter"), ("x", "parameter")]

  test "method calls resolve the receiver and arguments but not the method name" $
    expressionUses "x.missing(n)" ["x", "n"] (\expression => case expression.value of
      ExprMethodCall receiver _ arguments => Just (receiver :: arguments)
      _ => Nothing) `shouldBe` Right True

  test "field reads resolve the object but not the field name" $
    expressionUses "pair.missing" ["pair"] (\expression => case expression.value of
      ExprField object _ => Just [object]
      _ => Nothing) `shouldBe` Right True

  test "return values are resolved" $
    expressionUses "return x" ["x"] (\expression => case expression.value of
      ExprReturn (Just value) => Just [value]
      _ => Nothing) `shouldBe` Right True

  test "break values are resolved inside the loop body" $
    checkSource "fn f(x: i32) { loop { break x; } }" valueReferenceKinds
      `shouldBe` Right [("x", "parameter")]

  test "a while condition cannot see locals of its body" $
    unresolved "fn f() { while c { let c = true; } }" "c" `shouldBe` Right True

  test "locals declared in an if condition block do not reach the branches" $
    unresolved "fn f() { if { let c = true; c } { c; } }" "c" `shouldBe` Right True

  test "a parameter shadows its own function's name" $
    checkSource "fn f(f: i32) { f; }" valueReferenceKinds `shouldBe` Right [("f", "parameter")]

  test "a for binder cannot escape an enclosing block" $
    unresolved "fn f() { { for i in [1] {} } i; }" "i" `shouldBe` Right True

  test "leaving a for loop nested in a block restores the outer binding" $
    checkSource "fn f() { let i = 0; { for i in [1] { i; } } i; }" (\resolved => do
      (_, fn) <- functionNamed "f" resolved
      outerBinding <- letAt 0 fn.functionBody
      outer <- binder outerBinding.letPattern
      after <- exprAt 2 fn.functionBody
      block <- exprAt 1 fn.functionBody >>= blockBody
      loop <- exprAt 0 block
      ExprFor pattern _ body <- pure loop.value | _ => Nothing
      loopName <- binder pattern
      inner <- exprAt 0 body
      innerOK <- useMatches resolved loopName inner
      afterOK <- useMatches resolved outer after
      pure (innerOK && afterOK && symbolId loopName /= symbolId outer)) `shouldBe` Right True

  test "a constant initializer cannot see function parameters" $
    unresolved "fn f(x: i32) {} const C: i32 = x;" "x" `shouldBe` Right True

  test "an unresolved assignment target is reported" $
    unresolved "fn f() { y = 1; }" "y" `shouldBe` Right True

  test "function-type parameter names are not bindings" $
    unresolved "fn f(g: fn(x: i32) -> i32) { x; }" "x" `shouldBe` Right True

  test "an array length inside a function type cannot use a local" $
    nonConstantUse "fn f() { let n = 2; let g: fn(a: [i32; n]); }"
      `shouldBe` Right ("n", (1, 40, 1, 41), (1, 14, 1, 15))

  test "an assignment inside a constant expression cannot target an enclosing local" $
    nonConstantUse "fn f() { let mut x = 1; [0; { x = 2; 2 }]; }"
      `shouldBe` Right ("x", (1, 31, 1, 32), (1, 18, 1, 19))

  test "a parameter named like a prelude function is still a local in a constant expression" $
    nonConstantUse "fn f(abs: i32) { [0; abs]; }"
      `shouldBe` Right ("abs", (1, 22, 1, 25), (1, 6, 1, 9))

  test "constant item types and initializers may use constants as array lengths" $
    checkSource "const N: i32 = 2; const A: [i32; N] = [0; N];" valueReferenceKinds
      `shouldBe` Right [("N", "constant"), ("N", "constant")]

  test "a parameter type cannot use an earlier parameter as an array length" $
    nonConstantUse "fn f(n: i32, a: [i32; n]) {}"
      `shouldBe` Right ("n", (1, 23, 1, 24), (1, 6, 1, 7))

  test "a return type cannot use a parameter as an array length" $
    nonConstantUse "fn f(n: i32) -> [i32; n] {}"
      `shouldBe` Right ("n", (1, 23, 1, 24), (1, 6, 1, 7))

  test "a parameter type cannot use its own parameter as an array length" $
    nonConstantUse "fn f(n: [i32; n]) {}"
      `shouldBe` Right ("n", (1, 15, 1, 16), (1, 6, 1, 7))

  test "a parameter shadows a module function inside later signature types" $
    nonConstantUse "const fn n() -> i32 { 2 } fn f(n: i32, values: [i32; n()]) {}"
      `shouldBe` Right ("n", (1, 54, 1, 55), (1, 32, 1, 33))

  test "a parameter type sees a later parameter and rejects it as a constant" $
    nonConstantUse "fn f(a: [i32; n], n: i32) {}"
      `shouldBe` Right ("n", (1, 15, 1, 16), (1, 19, 1, 20))

  test "a later parameter shadows a module function in an earlier signature type" $
    nonConstantUse "const fn n() -> i32 { 2 } fn f(values: [i32; n()], n: i32) {}"
      `shouldBe` Right ("n", (1, 46, 1, 47), (1, 52, 1, 53))

  test "a later parameter shadows a prelude function in an earlier signature type" $
    nonConstantUse "fn f(values: [i32; abs(2)], abs: i32) {}"
      `shouldBe` Right ("abs", (1, 20, 1, 23), (1, 29, 1, 32))

  test "a local in a signature length block shadows an already registered later parameter" $
    checkSource "fn f(values: [i32; { let n = 2; n }], n: i32) { n; }" valueReferenceKinds
      `shouldBe` Right [("n", "local"), ("n", "parameter")]

  test "constant parameter patterns keep signature types and the body bound to the constant" $
    checkSource "const N: i32 = 2; fn f(values: [i32; N], N: i32) -> [i32; N] { N; }" (\resolved => do
      (_, con) <- constantNamed "N" resolved
      (_, fn) <- functionNamed "f" resolved
      [_, parameter] <- pure fn.functionParameters | _ => Nothing
      [_, name] <- parameterNames fn | _ => Nothing
      uses <- valueReferenceKinds resolved
      pure (constantOccurrenceMatches resolved con.constName parameter.astInfo.nodeId name &&
            uses == [("N", "constant"), ("N", "constant"), ("N", "constant")] &&
            length (SortedMap.toList resolved.tables.localVariables) == 1)) `shouldBe` Right True

  test "signature array lengths may use module constants alongside parameters" $
    checkSource "const N: i32 = 2; fn f(n: i32, a: [i32; N]) -> [i32; N] {}" valueReferenceKinds
      `shouldBe` Right [("N", "constant"), ("N", "constant")]

  test "a mutable let binder cannot shadow a constant declared later in the module" $
    constantShadowing "fn f() { let mut N = 1; }\nconst N: i32 = 2;"
      `shouldBe` Right ("N", (1, 18, 1, 19), (2, 7, 2, 8))

  -- Only constants are protected: mutable binders may shadow functions.
  test "mutable binders may shadow module and prelude functions" $
    checkSource "fn g() {} fn f() { let mut g = 1; let mut sin = 2; g; sin; }" valueReferenceKinds
      `shouldBe` Right [("g", "local"), ("sin", "local")]

  test "an immutable parameter named like a later constant is a constant pattern" $
    checkSource "fn f(U: ()) { U; } const U: () = ();" (\resolved => do
      (_, con) <- constantNamed "U" resolved
      (_, fn) <- functionNamed "f" resolved
      [parameter] <- pure fn.functionParameters | _ => Nothing
      [name] <- parameterNames fn | _ => Nothing
      use <- exprAt 0 fn.functionBody
      useOK <- useMatches resolved con.constName use
      pure (constantOccurrenceMatches resolved con.constName parameter.astInfo.nodeId name && useOK &&
            null (SortedMap.toList resolved.tables.localVariables))) `shouldBe` Right True

  test "a constant parameter pattern does not hide later duplicate parameters" $
    duplicateBinder "const U: () = (); fn f(U: (), x: i32, x: i32) {}"
      `shouldBe` Right ("x", (1, 39, 1, 40), (1, 31, 1, 32))

  test "a constant pattern between duplicate binders does not hide the duplicate" $
    duplicateBinder "const U: () = (); fn f() { let (x, U, x) = (1, (), 2); }"
      `shouldBe` Right ("x", (1, 39, 1, 40), (1, 33, 1, 34))

  test "a binder repeated three times reports the first repetition" $
    duplicateBinder "fn f() { let (x, x, x) = (1, 2, 3); }"
      `shouldBe` Right ("x", (1, 18, 1, 19), (1, 15, 1, 16))

  test "a repeat count in a constant initializer cannot use the initializer's local" $
    nonConstantUse "const C: i32 = { let x = 1; [0; x]; 2 };"
      `shouldBe` Right ("x", (1, 33, 1, 34), (1, 22, 1, 23))

  test "a constant initializer block may use its own locals" $
    checkSource "const C: i32 = { let x = 1; x };" valueReferenceKinds
      `shouldBe` Right [("x", "local")]

  test "a local inside a repeat count may shadow an outer parameter" $
    checkSource "fn f(n: i32) { [0; { let n = 1; n }]; }" valueReferenceKinds
      `shouldBe` Right [("n", "local")]

  test "a local initializer inside a repeat count cannot use an outer parameter" $
    nonConstantUse "fn f(n: i32) { [0; { let k = n; k }]; }"
      `shouldBe` Right ("n", (1, 30, 1, 31), (1, 6, 1, 7))

  test "a parameter shadows a module function inside the return type" $
    nonConstantUse "const fn n() -> i32 { 2 }\nfn f(n: i32) -> [i32; n()] {}"
      `shouldBe` Right ("n", (2, 23, 2, 24), (2, 6, 2, 7))

  -- As in Rust (E0070), assigning to a constant or function is a type error,
  -- not a resolution error: the target resolves to that item.
  test "assignment targets may resolve to constants and functions" $
    checkSource "const N: i32 = 1; fn g() {} fn f() { N = 2; g = 3; }" (\resolved => do
      (_, con) <- constantNamed "N" resolved
      (_, g) <- functionNamed "g" resolved
      (_, f) <- functionNamed "f" resolved
      constantAssignment <- assignmentAt 0 f.functionBody
      functionAssignment <- assignmentAt 1 f.functionBody
      AssignTargetName constantTarget <- pure constantAssignment.assignmentTarget.value | _ => Nothing
      AssignTargetName functionTarget <- pure functionAssignment.assignmentTarget.value | _ => Nothing
      pure (symbolId constantTarget == symbolId con.constName &&
            symbolId functionTarget == symbolId g.functionName &&
            referenceMatches resolved AssignmentTarget constantAssignment.assignmentTarget.astInfo.nodeId constantTarget &&
            referenceMatches resolved AssignmentTarget functionAssignment.assignmentTarget.astInfo.nodeId functionTarget &&
            null (SortedMap.toList resolved.tables.localVariables))) `shouldBe` Right True
