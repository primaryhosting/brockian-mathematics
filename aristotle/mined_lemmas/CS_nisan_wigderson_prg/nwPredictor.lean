import Mathlib

/-!
# Nisan Wigderson Prg
Category: Frontier Cs
Target: CS.nisan_wigderson_prg
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

open Finset

/-- Real-valued indicator of a Boolean value. -/

def nwPredictor (G : Fin m → (Fin ℓ → Bool) → Bool) (D : (Fin m → Bool) → Bool)
    (i : Fin m) (r : Fin m → Bool) (c : Bool) (x : Fin ℓ → Bool) : Bool :=
  xor c (if D (hybridStr G i x r) then r i else !(r i))

/-- Probability (over the seed `x`) that the predictor correctly computes the `i`-th
generator component `G i`. -/
