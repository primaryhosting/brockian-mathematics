/-
# Nisan Wigderson Prg
Category: Frontier Cs
Target: CS.nisan_wigderson_prg
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Finset
open scoped BigOperators

namespace CS

/-! ### Basic probabilistic vocabulary

All probabilities are uniform probabilities over finite types, expressed as expectations
of `{0,1}`-valued indicator functions. -/

/-- The `{0,1}`-valued indicator of a boolean. -/

noncomputable def hybProb {n m ℓ : ℕ} (S : Fin m → Fin n → Fin ℓ) (f : (Fin n → Bool) → Bool)
    (D : (Fin m → Bool) → Bool) (t : ℕ) : ℝ :=
  pr fun p : (Fin ℓ → Bool) × (Fin m → Bool) => D (hyb S f t p.1 p.2)

/-- Overwrite the coordinates in the range of `σ` of `x0` by the bits of `z`. -/
