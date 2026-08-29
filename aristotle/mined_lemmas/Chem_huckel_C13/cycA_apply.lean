/-
# Huckel C 13
Category: Chemistry
Target: Chem.huckel_C13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Polynomial Finset

namespace Chem

/-! ### The cyclic shift operator -/

/-- The cyclic shift endomorphism of `Fin 13 → ℂ`, `f ↦ (i ↦ f (i + 1))`. -/

lemma cycA_apply (f : Fin 13 → ℂ) (i : Fin 13) : cycA f i = f (i + 1) + f (i + 12) := by
  show shift f i + (shift ^ 12) f i = _
  rw [shift_apply, shift_pow_apply, show (12 : ℕ) • (1 : Fin 13) = 12 from by decide]

