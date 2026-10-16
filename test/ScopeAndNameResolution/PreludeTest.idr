module ScopeAndNameResolution.PreludeTest

import Compiler.Prelude
import Compiler.ScopeAndNameResolution.Data
import Compiler.ScopeAndNameResolution.Validate
import Frontend.ASTData
import Frontend.Source
import ScopeAndNameResolution.Helper
import ScopeAndNameResolution.PreludeTestHelper

import Data.List
import Data.Maybe
import Data.SortedMap
import Test.Simple

%default total

export
runPreludeFunctionsResolutionTests : IO ()
runPreludeFunctionsResolutionTests = runTests $ Test.do
  test "prelude ownership, bindings and declaration order are complete" $
    (resolvedSource "fn f() { sin(0.0); }" >>= preludeLayout) `shouldBe` Just True

  test "every specified prelude name resolves as an ordinary value" $
    useOrigins "fn f() { abs; acos; asin; atan; ceil; cos; exp; floor; ln; log2; log10; max; min; Param; phase; round; sin; sqrt; tan; turns; I; X; Y; Z; H; S; SDG; T; TDG; SX; SXDG; RX; RY; RZ; U1; U2; U3; CNOT; CX; CY; CZ; CS; CSDG; CT; CTDG; CSX; CSXDG; CRX; CRY; CRZ; CU1; CU2; CU3; SWAP; RXX; RYY; RZZ; CCX; CSWAP; GPI; GPI2; MS; ZZ; }"
      `shouldBe` Just (map (\name => (name, "prelude")) preludeFunctionNames)

  test "source functions shadow the prelude even before their declaration" $
    useOrigins "fn f() { sin(0.0); } fn sin(x: f64) { x; }"
      `shouldBe` Just [("sin", "function"), ("x", "parameter")]

  test "parameter bindings shadow prelude functions" $
    useOrigins "fn f(sin: i32) { sin; }"
      `shouldBe` Just [("sin", "parameter")]

  test "local declarations can shadow prelude quantum gates" $
    useOrigins "fn f() { H; let H = 1; H; }"
      `shouldBe` Just [("H", "prelude"), ("H", "local")]

  test "a local initializer sees the prelude before the new binding" $
    useOrigins "fn f() { let sin = sin; sin; }"
      `shouldBe` Just [("sin", "prelude"), ("sin", "local")]

  test "block-local shadowing does not replace the prelude outside the block" $
    useOrigins "fn f() { sin; { let sin = 1; sin; } sin; }"
      `shouldBe` Just [("sin", "prelude"), ("sin", "local"), ("sin", "prelude")]

  test "prelude lookup still reports unknown names" $
    missingName "fn f() { unknown_function(); }" `shouldBe` Just "unknown_function"

  test "prelude registration does not suppress duplicate source declarations" $
    (case resolveSource "fn sin() {} fn sin() {}" of
       Left (ResolutionFailure (DuplicateDeclaration "sin" [_] current previous)) =>
         spanKey current == ("", 1, 16, 1, 19) &&
         spanKey previous == ("", 1, 4, 1, 7)
       _ => False) `shouldBe` True

  test "prelude registration creates no source occurrences or locals" $
    (do resolved <- resolvedSource ""
        root <- lookup resolved.rootScope resolved.tables.scopes
        pure (length (SortedMap.toList resolved.tables.references),
              length (SortedMap.toList resolved.tables.nodeScopes),
              length (SortedMap.toList resolved.tables.localVariables),
              length (SortedMap.toList root.valueBindings),
              length (SortedMap.toList root.typeBindings)))
      `shouldBe` Just (0, 1, 0, 0, 0)

  test "repeated prelude uses retain their symbol identity and use-site scopes" $
    (do resolved <- resolvedSource "fn f() { sin; { sin; } }"
        [first, second] <- pure (valueReferences resolved)
          | _ => Nothing
        pure (first.target == second.target &&
              first.enclosingScope /= second.enclosingScope &&
              lookup first.occurrence.nodeId resolved.tables.nodeScopes == Just first.enclosingScope &&
              lookup second.occurrence.nodeId resolved.tables.nodeScopes == Just second.enclosingScope))
      `shouldBe` Just True

  test "resolved prelude and shadowing tables pass invariant validation" $
    traverse (\source => map (map show . validateResolvedModule) (resolvedSource source))
      [ ""
      , "fn f() { sin(0.0); cos(0.0); }"
      , "fn f() { sin(0.0); } fn sin(x: f64) { x; }"
      , "fn f() { let sin = sin; sin; }"
      ] `shouldBe` Just [[], [], [], []]

  test "a later source constant shadows a Prelude function without changing its registration" $
    checkSource "fn f() { sin; } const sin: i32 = 1;" constantShadowsPrelude `shouldBe` Right True
