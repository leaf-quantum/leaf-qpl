module Frontend.QuantumAnnotations

import Frontend.Syntax.Common

%default total

public export
data QuantumCleanup
  = NoAutomaticCleanup
  | ScratchCleanup
  | UncomputeOnReturn

public export
record QuantumStorageProperties where
  constructor MkQuantumStorageProperties
  usage   : QuantumMultiplicityQualifier
  cleanup : QuantumCleanup
