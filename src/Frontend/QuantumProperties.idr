module Frontend.QuantumProperties

import Frontend.ASTData

%default total

public export
data QubitTypeQualifier
  = Linear
  | Affine

public export
record QuantumStorageProperties where
  constructor MkQuantumStorageProperties
  usage   : QubitTypeQualifier
  scratch : Bool
