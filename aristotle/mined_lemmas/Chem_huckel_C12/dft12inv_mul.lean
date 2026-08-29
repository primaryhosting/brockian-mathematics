import Mathlib

/-!
# Huckel C 12
Category: Chemistry
Target: Chem.huckel_C12
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real

set_option maxHeartbeats 1000000

namespace Chem

open Complex Polynomial Matrix Finset

/-- The primitive 12-th root of unity `exp(2πi/12)`. -/

lemma dft12inv_mul : dft12inv * dft12 = 1 := by
  ext j l
  rw [Matrix.mul_apply]
  have hstep : ∀ k : ZMod 12,
      dft12inv j k * dft12 k l = (12 : ℂ)⁻¹ * zeta12 (k * (l - j)) := by
    intro k
    have h : -(j * k) + k * l = k * (l - j) := by ring
    simp only [dft12, dft12inv]
    rw [← h, zeta12_add]
    ring
  rw [Finset.sum_congr rfl (fun k _ => hstep k), ← Finset.mul_sum, sum_zeta12_mul]
  by_cases h : j = l
  · subst h; simp
  · have hjl : l - j ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
    rw [if_neg hjl, Matrix.one_apply_ne h]
    ring

/-- `ζ^k + ζ^{-k} = 2 cos(2πk/12)`. -/
