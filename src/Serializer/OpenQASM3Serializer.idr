module Serializer.OpenQASM3Serializer

import Data.Fin
import Data.Nat
import Data.Vect
import DSL.Core    -- Radians, MkRadians, pi, Num / Neg
import DSL.Gates   -- UnitaryGate, etc.

%default total

--------------------------------------------------------------------------------
-- Helpers: indices, qbit pretty-printers, list helpers
--------------------------------------------------------------------------------

public export
qasmIndex : {n : Nat} -> Fin n -> String
qasmIndex i = show (finToNat i)

public export
qasmQbit : {n : Nat} -> String -> Fin n -> String
qasmQbit qreg q = qreg ++ "[" ++ qasmIndex q ++ "]"

public export
angleToStr : Radians -> String
angleToStr = show

public export
vectToList : Vect n a -> List a
vectToList []        = []
vectToList (x :: xs) = x :: vectToList xs

public export
concatStrings : List String -> String
concatStrings []        = ""
concatStrings (x :: xs) = x ++ concatStrings xs

public export
joinWith : String -> List String -> String
joinWith sep []        = ""
joinWith sep [x]       = x
joinWith sep (x :: xs) = x ++ sep ++ joinWith sep xs

--------------------------------------------------------------------------------
-- Core representation: a gate + (possibly) ctrl/negctrl modifiers
--
-- ctrls: one Bool per control qbit at the START of 'qbits'
--        True  = ctrl    @   (control on |1>)
--        False = negctrl @   (control on |0>)
--------------------------------------------------------------------------------

public export
record CoreGate (n : Nat) where
  constructor MkCoreGate
  ctrls  : List Bool
  gname  : String
  params : List Radians
  qbits : List (Fin n)

--------------------------------------------------------------------------------
-- Flatten UnitaryGate (including Controlled wrapper) into CoreGate
--------------------------------------------------------------------------------

public export
unitaryToCore : UnitaryGate n -> CoreGate n

-- 1-qbit (Clifford + T and friends)

unitaryToCore (Id q)    = MkCoreGate [] "id"   [] [q]
unitaryToCore (X q)     = MkCoreGate [] "x"    [] [q]
unitaryToCore (Y q)     = MkCoreGate [] "y"    [] [q]
unitaryToCore (Z q)     = MkCoreGate [] "z"    [] [q]
unitaryToCore (H q)     = MkCoreGate [] "h"    [] [q]
unitaryToCore (S q)     = MkCoreGate [] "s"    [] [q]
unitaryToCore (SDG q)   = MkCoreGate [] "sdg"  [] [q]
unitaryToCore (T q)     = MkCoreGate [] "t"    [] [q]
unitaryToCore (TDG q)   = MkCoreGate [] "tdg"  [] [q]
unitaryToCore (SX q)    = MkCoreGate [] "sx"   [] [q]
unitaryToCore (SXDG q)  = MkCoreGate [] "sxdg" [] [q]   -- user-defined gate in QASM3

-- Parametric 1-qbit rotations

unitaryToCore (RX th q) = MkCoreGate [] "rx" [th] [q]
unitaryToCore (RY th q) = MkCoreGate [] "ry" [th] [q]
unitaryToCore (RZ th q) = MkCoreGate [] "rz" [th] [q]

-- U-family (you can map these to stdgates.inc semantics or keep as user gates)

unitaryToCore (U th ph la q) =
  MkCoreGate [] "U" [th, ph, la] [q]

unitaryToCore (U1 la q) =
  MkCoreGate [] "u1" [la] [q]

unitaryToCore (U2 ph la q) =
  MkCoreGate [] "u2" [ph, la] [q]

unitaryToCore (U3 th ph la q) =
  MkCoreGate [] "u3" [th, ph, la] [q]

-- 2-qbit gates

unitaryToCore (CNOT c t {neq}) =
  MkCoreGate [] "cx" [] [c, t]

unitaryToCore (CY c t {neq}) =
  MkCoreGate [] "cy" [] [c, t]

unitaryToCore (CZ c t {neq}) =
  MkCoreGate [] "cz" [] [c, t]

unitaryToCore (CH c t {neq}) =
  MkCoreGate [] "ch" [] [c, t]

unitaryToCore (CS c t {neq}) =
  MkCoreGate [] "cs" [] [c, t]

unitaryToCore (CSDG c t {neq}) =
  MkCoreGate [] "csdg" [] [c, t]

unitaryToCore (CT c t {neq}) =
  MkCoreGate [] "ct" [] [c, t]

unitaryToCore (CTDG c t {neq}) =
  MkCoreGate [] "ctdg" [] [c, t]

unitaryToCore (CSX c t {neq}) =
  MkCoreGate [] "csx" [] [c, t]

unitaryToCore (CSXDG c t {neq}) =
  MkCoreGate [] "csxdg" [] [c, t]

-- Controlled parametric rotations / U-family

unitaryToCore (CRX th c t {neq}) =
  MkCoreGate [] "crx" [th] [c, t]

unitaryToCore (CRY th c t {neq}) =
  MkCoreGate [] "cry" [th] [c, t]

unitaryToCore (CRZ th c t {neq}) =
  MkCoreGate [] "crz" [th] [c, t]

unitaryToCore (CU1 la c t {neq}) =
  MkCoreGate [] "cu1" [la] [c, t]

unitaryToCore (CU2 ph la c t {neq}) =
  MkCoreGate [] "cu2" [ph, la] [c, t]

unitaryToCore (CU3 th ph la c t {neq}) =
  MkCoreGate [] "cu3" [th, ph, la] [c, t]

-- Two-qbit non-controlled interactions

unitaryToCore (SWAP a b {neq}) =
  MkCoreGate [] "swap" [] [a, b]

unitaryToCore (RXX th a b {neq}) =
  MkCoreGate [] "rxx" [th] [a, b]

unitaryToCore (RYY th a b {neq}) =
  MkCoreGate [] "ryy" [th] [a, b]

unitaryToCore (RZZ th a b {neq}) =
  MkCoreGate [] "rzz" [th] [a, b]

unitaryToCore (RZX th a b {neq}) =
  MkCoreGate [] "rzx" [th] [a, b]

-- 3-qbit gates

unitaryToCore (CCX c1 c2 t {d12} {d1t} {d2t}) =
  MkCoreGate [] "ccx" [] [c1, c2, t]

unitaryToCore (CSWAP c a b {cab} {ca} {cb}) =
  MkCoreGate [] "cswap" [] [c, a, b]

-- Generic Controlled wrapper:
-- We FLATTEN all nested controls into:
--   - extra Bool flags at the FRONT of 'ctrls'
--   - extra control qbits at the FRONT of 'qbits'
--
-- So the resulting CoreGate qbits list is: [all controls] ++ [inner’s qbits]
-- and ctrls: [polarity for each control] ++ inner.ctrls

unitaryToCore (Controlled {k} cs bs inner) =
  let
    innerCore : CoreGate n
    innerCore = unitaryToCore inner

    ctrls0  : List Bool
    ctrls0  = ctrls innerCore

    name0   : String
    name0   = gname innerCore

    params0 : List Radians
    params0 = params innerCore

    qbits0 : List (Fin n)
    qbits0 = qbits innerCore

    csList : List (Fin n)
    csList = vectToList cs

    bsList : List Bool
    bsList = vectToList bs
  in
    MkCoreGate (List.(++) bsList ctrls0) name0 params0 (List.(++) csList qbits0)

--------------------------------------------------------------------------------
-- CoreGate -> OpenQASM 3 statement
--
-- We emit:
--   ctrl @ ... @ negctrl @ gname(theta, ...) q[...], q[...], ...;
--
-- Number of ctrl/negctrl = length ctrls
-- Number of leading qbits used as controls = SAME length
--------------------------------------------------------------------------------

public export
coreGateToOpenQasm3 :
  {n : Nat} ->
  (qregName : String) ->
  CoreGate n ->
  String
coreGateToOpenQasm3 qregName (MkCoreGate ctrls name params qbits) =
  let
    -- One modifier per control qbit, in order.
    mods : List String
    mods = map (\b => if b then "ctrl @ " else "negctrl @ ") ctrls

    modsStr : String
    modsStr = concatStrings mods

    paramsStr : String
    paramsStr =
      case params of
        []    => ""
        ps    => "(" ++ joinWith ", " (map angleToStr ps) ++ ")"

    qbitsStr : String
    qbitsStr =
      joinWith ", " (map (qasmQbit qregName) qbits)
  in
    modsStr ++ name ++ paramsStr ++ " " ++ qbitsStr ++ ";"

--------------------------------------------------------------------------------
-- Public entry: UnitaryGate n -> OpenQASM 3 line
--------------------------------------------------------------------------------

public export
unitaryToOpenQasm3 :
  {n : Nat} ->
  (qregName : String) ->
  UnitaryGate n ->
  String
unitaryToOpenQasm3 qregName u =
  coreGateToOpenQasm3 qregName (unitaryToCore u)
