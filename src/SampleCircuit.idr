
module SampleCircuit

import Data.Fin
import DSL.Circuit
import DSL.Core
import DSL.Gates
import DSL.GateHelpers
import DSL.Helpers

%foreign "scheme:lambda (msg) (let ((loc (##sys#current-source-location))) (if loc (raise (make-compile-time-error msg loc)) (raise (make-exn msg '()))))"
prim_panic : String -> a

partial
panic : String -> a
panic msg = prim_panic msg

public export
build : Circuit 5 5
build = c13
  where
  -- choose wires via literals; proofs below ensure equality branches crash
  q0 = fromLiteral {n = 5} 0
  q1 = fromLiteral {n = 5} 1
  q2 = fromLiteral {n = 5} 2
  q3 = fromLiteral {n = 5} 3
  q4 = fromLiteral {n = 5} 4

  -- start empty
  c0  = emptyCircuit {n = 5}

  -- 1-qbit gates
  c1  = hadamard q0 c0
  c2  = s q1 c1
  c3  = rotY (MkRadians 1.234) q2 c2

  -- 2-qbit, controlled rotations, and interactions
  c4  = case mkNeq q0 q1 of
    Just neq => cnot q0 q1 {neq = neq} c3
    Nothing  => panic "CNOT requires distinct wires"
  c5  = case mkNeq q1 q2 of
    Just neq => ctrlRZ (MkRadians 0.25) q1 q2 {neq = neq} c4
    Nothing  => panic "ctrlRZ requires distinct wires"
  c6  = case mkNeq q2 q3 of
    Just neq => rzx (MkRadians 0.5) q2 q3 {neq = neq} c5
    Nothing  => panic "rzx requires distinct wires"
  c7  = case mkNeq q3 q4 of
    Just neq => swap q3 q4 {neq = neq} c6
    Nothing  => panic "swap requires distinct wires"
  c8  = u3 (MkRadians 0.7) (MkRadians 0.1) (MkRadians 0.2) q4 c7
  c9  = case mkNeq q0 q4 of
    Just neq => ctrlSX q0 q4 {neq = neq} c8
    Nothing  => panic "ctrlSX requires distinct wires"

  -- measurement & reset (non-unitaries)
  c10 = measure q0 c9 
  c11 = reset q3 c10 

  -- continue with unitary ops on unmeasured lines
  c12 = case mkNeq q1 q2 of
    Just neq => rzz (MkRadians 0.33) q1 q2 {neq = neq} c11
    Nothing  => panic "rzz requires distinct wires"
  c13 = tDag q2 c12
