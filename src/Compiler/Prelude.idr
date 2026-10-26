module Compiler.Prelude

%default total

public export
preludeFunctionNames : List String
preludeFunctionNames = 
  [
    "abs",
    "acos",
    "asin",
    "atan",
    "ceil",
    "cos",
    "exp",
    "floor",
    "ln",
    "log2",
    "log10",
    "max",
    "min",
    "Param",
    "phase",
    "round",
    "sin",
    "sqrt",
    "tan",
    "turns",
    -- Quantum gates
    "I", "X", "Y", "Z", "H", "S", "SDG", "T", "TDG", "SX", "SXDG",
    "RX", "RY", "RZ", "U1", "U2", "U3", "CNOT", "CX", "CY", "CZ",
    "CS", "CSDG", "CT", "CTDG", "CSX", "CSXDG", "CRX", "CRY", "CRZ",
    "CU1", "CU2", "CU3", "SWAP", "RXX", "RYY", "RZZ", "CCX", "CSWAP",
    "GPI", "GPI2", "MS", "ZZ"
  ]
