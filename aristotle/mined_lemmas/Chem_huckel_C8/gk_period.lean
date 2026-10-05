/-
# Huckel C 8
Category: Chemistry
Target: Chem.huckel_C8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 8
Category: Chemistry
Target: Chem.huckel_C8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Real Matrix SimpleGraph

namespace Chem

/-- The adjacency matrix (over `ℝ`) of the cycle graph `C₈`, i.e. the Hückel matrix of
cyclooctatetraene in units where `α = 0` and `β = 1`. -/

lemma gk_period (k : ℕ) (m t : ℤ) : gk k (m + 8 * t) = gk k m := by
  have h : theta k * ((m + 8 * t : ℤ) : ℝ) = theta k * (m : ℝ) + (((k : ℤ) * t : ℤ) : ℝ) * (2 * π) := by
    unfold theta; push_cast; ring
  unfold gk
  rw [h, Real.cos_add_int_mul_two_pi]

