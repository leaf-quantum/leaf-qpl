module DSL.Core

%default total

public export
data Radians = MkRadians Double

public export
Num Radians where
  (+) (MkRadians x) (MkRadians y) = MkRadians (x + y)
  (*) (MkRadians x) (MkRadians y) = MkRadians (x * y)
  fromInteger i = MkRadians (cast i)

public export
Neg Radians where
  negate (MkRadians x) = MkRadians (negate x)
  (-) x y = x + negate y

public export
Show Radians where
  show (MkRadians x) = show x

public export
pi : Radians
pi = MkRadians 3.141592653589793

-- public export
-- Qbit : Type
-- Qbit = Nat     -- wire label/index

-- public export
-- record Complex where
--   constructor MkComplex
--   re, im : Double

-- public export
-- data QbitState
--   = Zero
--   | One
--   | Superposition Complex Complex  -- amplitudes α, β
