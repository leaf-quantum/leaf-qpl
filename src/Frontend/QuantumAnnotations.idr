module Frontend.QuantumAnnotations

import Frontend.Syntax.Common

%default total

public export
record QuantumStorageProperties where
  constructor MkQuantumStorageProperties
  usage   : QuantumMultiplicityQualifier
  scratch : Bool
