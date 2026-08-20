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

lemma mem_shift_spectrum (n : ℕ) [NeZero n] (μ : ℂ) (h : μ ^ n = 1) :
    μ ∈ spectrum ℂ (shift n) := by
  set v : ZMod n → ℂ := fun j => μ ^ j.val with hv
  have hv0 : v ≠ 0 := by
    intro hc
    have : v 0 = 0 := by rw [hc]; rfl
    simp [hv] at this
  have hstep : ∀ i : ZMod n, v (i + 1) = μ * v i := fun i => geom_vec_succ n μ h i
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_ne_iff,
    ← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨v, hv0, ?_⟩
  funext i
  simp only [Matrix.sub_mulVec, Pi.sub_apply, shift_mulVec, hstep, Pi.zero_apply]
  simp [Matrix.algebraMap_eq_diagonal, Matrix.mulVec_diagonal]

/-- The spectrum of the cyclic shift matrix is exactly the set of `n`-th roots of unity. -/
