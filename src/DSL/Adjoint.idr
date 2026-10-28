module DSL.Adjoint

import Data.Fin
import DSL.Control
import DSL.Core
import DSL.Gates

public export
adjointUnitary : UnitaryGate n -> UnitaryGate n

-- 1-qbit Clifford + T
adjointUnitary (Id q)    = Id q
adjointUnitary (X q)     = X q
adjointUnitary (Y q)     = Y q
adjointUnitary (Z q)     = Z q
adjointUnitary (H q)     = H q
adjointUnitary (S q)     = SDG q
adjointUnitary (SDG q)   = S q
adjointUnitary (T q)     = TDG q
adjointUnitary (TDG q)   = T q
adjointUnitary (SX q)    = SXDG q
adjointUnitary (SXDG q)  = SX q

-- Parametric rotations (assuming Radians is a Num)
adjointUnitary (RX theta q) = RX (-theta) q
adjointUnitary (RY theta q) = RY (-theta) q
adjointUnitary (RZ theta q) = RZ (-theta) q

-- U-family
adjointUnitary (U  theta phi lambda q) =
  U (-theta) (-lambda) (-phi) q

adjointUnitary (U1 lambda q) =
  U1 (-lambda) q

-- For U2, we use the standard OpenQASM / Qiskit adjoint:
-- U2(φ, λ)† = U2(-λ - π, -φ + π), up to global phase
adjointUnitary (U2 phi lambda q) =
  U2 (-lambda - pi) ( -phi + pi ) q

adjointUnitary (U3 theta phi lambda q) =
  U3 (-theta) (-lambda) (-phi) q

-- 2-qbit + 3-qbit: many of these are self-adjoint
adjointUnitary (CNOT c t {neq})     = CNOT c t {neq = neq}
adjointUnitary (CY c t {neq})       = CY c t {neq = neq}
adjointUnitary (CZ c t {neq})       = CZ c t {neq = neq}
adjointUnitary (CH c t {neq})       = CH c t {neq = neq}
adjointUnitary (CS c t {neq})       = CSDG c t {neq = neq}
adjointUnitary (CSDG c t {neq})     = CS c t {neq = neq}
adjointUnitary (CT c t {neq})       = CTDG c t {neq = neq}
adjointUnitary (CTDG c t {neq})     = CT c t {neq = neq}
adjointUnitary (CSX c t {neq})      = CSXDG c t {neq = neq}
adjointUnitary (CSXDG c t {neq})    = CSX c t {neq = neq}

adjointUnitary (CRX theta c t {neq}) =
  CRX (-theta) c t {neq = neq}
adjointUnitary (CRY theta c t {neq}) =
  CRY (-theta) c t {neq = neq}
adjointUnitary (CRZ theta c t {neq}) =
  CRZ (-theta) c t {neq = neq}

adjointUnitary (CU1 lambda c t {neq}) =
  CU1 (-lambda) c t {neq = neq}
adjointUnitary (CU2 phi lambda c t {neq}) =
  CU2 (-lambda - pi) (-phi + pi) c t {neq = neq}
adjointUnitary (CU3 theta phi lambda c t {neq}) =
  CU3 (-theta) (-lambda) (-phi) c t {neq = neq}

adjointUnitary (SWAP a b {neq})     = SWAP a b {neq = neq}
adjointUnitary (RXX theta a b {neq}) =
  RXX (-theta) a b {neq = neq}
adjointUnitary (RYY theta a b {neq}) =
  RYY (-theta) a b {neq = neq}
adjointUnitary (RZZ theta a b {neq}) =
  RZZ (-theta) a b {neq = neq}
adjointUnitary (RZX theta a b {neq}) =
  RZX (-theta) a b {neq = neq}

adjointUnitary (CCX c1 c2 t {d12} {d1t} {d2t}) =
  CCX c1 c2 t {d12 = d12} {d1t = d1t} {d2t = d2t}

adjointUnitary (CSWAP c a b {cab} {ca} {cb}) =
  CSWAP c a b {cab = cab} {ca = ca} {cb = cb}

-- Controlled wrapper: adjoint just adjoints the inner gate
adjointUnitary (Controlled cs bs inner) =
  Controlled cs bs (adjointUnitary inner)

public export
adjointGate : Gate n -> Maybe (Gate n)
adjointGate (UGate u)   = Just (UGate (adjointUnitary u))
adjointGate (Measure _) = Nothing   -- not unitary
adjointGate (Reset   _) = Nothing   -- not unitary

  -- -- 1 control on |1⟩ (classic single control)
  -- let g1 : Gate n = mkControlled [c] [True] (X t)
  -- -- 1 control on |0⟩ (negative control)
  -- let g2 : Gate n = mkControlled [c] [False] (H t)
  -- -- 2 controls, mixed polarities
  -- let g3 : Gate n = mkControlled [c1, c2] [True, False] (RZ theta t)
  -- -- Add a control to a 2-qbit gate (e.g., controlled-SWAP)
  -- let g4 : Gate n = mkControlled [c] [True] (SWAP a b)
  -- -- Nesting: add another control later (e.g., build CCCX)
  -- let g5 : Gate n = mkControlled [d] [True] (mkControlled [c] [True] (X t))
  -- -- Controlled parametric gate (e.g., CU3)
  -- let g6 : Gate n = mkControlled [c] [True] (U3 th ph lam t)
