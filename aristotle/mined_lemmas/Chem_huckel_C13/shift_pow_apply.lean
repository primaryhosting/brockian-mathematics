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

lemma shift_pow_apply (m : ℕ) : ∀ (f : Fin 13 → ℂ) (i : Fin 13),
    (shift ^ m) f i = f (i + m • (1 : Fin 13)) := by
  induction m with
  | zero => intro f i; simp
  | succ m ih =>
      intro f i
      rw [pow_succ]
      show (shift ^ m) (shift f) i = _
      rw [ih (shift f) i, shift_apply, succ_nsmul, ← add_assoc]

