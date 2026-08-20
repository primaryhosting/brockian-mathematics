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

def hybridStr (G : Fin m → (Fin ℓ → Bool) → Bool) (k : ℕ)
    (x : Fin ℓ → Bool) (r : Fin m → Bool) : Fin m → Bool :=
  fun j => if (j : ℕ) < k then G j x else r j

/-- Unnormalised acceptance count of the distinguisher `D` on the `k`-th hybrid. -/
