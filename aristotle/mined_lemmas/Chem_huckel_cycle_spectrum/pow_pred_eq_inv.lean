/-
# Huckel Cycle Spectrum
Category: Chemistry
Target: Chem.huckel_cycle_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel Cycle Spectrum
Category: Chemistry
Target: Chem.huckel_cycle_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Polynomial

/-- The cyclic shift matrix on `ZMod n`: it sends the standard basis vector `e i` to
`e (i - 1)`, equivalently `(shift n).mulVec v i = v (i + 1)`. -/

lemma pow_pred_eq_inv (μ : ℂ) (n : ℕ) (hn : 1 ≤ n) (h : μ ^ n = 1) : μ ^ (n - 1) = μ⁻¹ := by
  have hμ : μ ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by omega)] at h
    exact zero_ne_one h
  have : μ ^ (n - 1) * μ = 1 := by
    rw [← pow_succ, Nat.sub_add_cancel hn, h]
  field_simp at this ⊢
  linear_combination this

/-- The `k`-th root of unity contributes the Hückel energy `2 cos (2 π k / n)`. -/
