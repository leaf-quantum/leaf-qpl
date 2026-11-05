module Compiler.TypeChecker.PreludeSignatures

import Compiler.TypeChecker.Data

%default total

public export
preludeSymbolType : String -> InferredType
preludeSymbolType "abs" = ?abs
preludeSymbolType "acos" = ?acos
preludeSymbolType "asin" = ?asin
preludeSymbolType "atan" = ?atan
preludeSymbolType "ceil" = ?ceil
preludeSymbolType "cos" = ?cos
preludeSymbolType "exp" = ?exp
preludeSymbolType "floor" = ?floor
preludeSymbolType "ln" = ?ln
preludeSymbolType "log2" = ?log2
preludeSymbolType "log10" = ?log10
preludeSymbolType "max" = ?max
preludeSymbolType "min" = ?min
preludeSymbolType "Param" = ?Param
preludeSymbolType "phase" = ?phase
preludeSymbolType "round" = ?round
preludeSymbolType "sin" = ?sin
preludeSymbolType "sqrt" = ?sqrt
preludeSymbolType "tan" = ?tan
preludeSymbolType "turns" = ?turns
preludeSymbolType "I" = ?I
preludeSymbolType "X" = ?X
preludeSymbolType "Y" = ?Y
preludeSymbolType "Z" = ?Z
preludeSymbolType "H" = ?H
preludeSymbolType "S" = ?S
preludeSymbolType "SDG" = ?SDG
preludeSymbolType "T" = ?T
preludeSymbolType "TDG" = ?TDG
preludeSymbolType "SX" = ?SX
preludeSymbolType "SXDG" = ?SXDG
preludeSymbolType "RX" = ?RX
preludeSymbolType "RY" = ?RY
preludeSymbolType "RZ" = ?RZ
preludeSymbolType "U1" = ?U1
preludeSymbolType "U2" = ?U2
preludeSymbolType "U3" = ?U3
preludeSymbolType "CNOT" = ?CNOT
preludeSymbolType "CX" = ?CX
preludeSymbolType "CY" = ?CY
preludeSymbolType "CZ" = ?CZ
preludeSymbolType "CS" = ?CS
preludeSymbolType "CSDG" = ?CSDG
preludeSymbolType "CT" = ?CT
preludeSymbolType "CTDG" = ?CTDG
preludeSymbolType "CSX" = ?CSX
preludeSymbolType "CSXDG" = ?CSXDG
preludeSymbolType "CRX" = ?CRX
preludeSymbolType "CRY" = ?CRY
preludeSymbolType "CRZ" = ?CRZ
preludeSymbolType "CU1" = ?CU1
preludeSymbolType "CU2" = ?CU2
preludeSymbolType "CU3" = ?CU3
preludeSymbolType "SWAP" = ?SWAP
preludeSymbolType "RXX" = ?RXX
preludeSymbolType "RYY" = ?RYY
preludeSymbolType "RZZ" = ?RZZ
preludeSymbolType "CCX" = ?CCX
preludeSymbolType "CSWAP" = ?CSWAP
preludeSymbolType "GPI" = ?GPI
preludeSymbolType "GPI2" = ?GPI2
preludeSymbolType "MS" = ?MS
preludeSymbolType "ZZ" = ?ZZ
preludeSymbolType symbolName = assert_total $ idris_crash "In function preludeSymbolType type for prelude symbol \{symbolName} is missing."
