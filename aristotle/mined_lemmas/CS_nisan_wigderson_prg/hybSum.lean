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

def hybSum (G : Fin m → (Fin ℓ → Bool) → Bool) (D : (Fin m → Bool) → Bool) (k : ℕ) : ℝ :=
  ∑ x : Fin ℓ → Bool, ∑ r : Fin m → Bool, ind (D (hybridStr G k x r))

/-- Acceptance probability of `D` on the `k`-th hybrid distribution. -/
