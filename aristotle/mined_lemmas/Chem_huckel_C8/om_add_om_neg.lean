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

namespace Chem

/-- The adjacency matrix of the cycle graph `C₈`, indexed by `ZMod 8`
(vertex `i` is adjacent to `i + 1` and `i - 1`), with complex entries. -/

lemma om_add_om_neg (k : ZMod 8) :
    om k + om (-k) = ((2 * Real.cos (2 * Real.pi * (k.val : ℝ) / 8) : ℝ) : ℂ) := by
  have hk : om k * om (-k) = 1 := by rw [← om_add, add_neg_cancel, om_zero]
  have h1 : om k ≠ 0 := by
    intro h; rw [h, zero_mul] at hk; exact zero_ne_one hk
  have h2 : om (-k) = (om k)⁻¹ := by
    field_simp
    linear_combination hk
  rw [h2, om_eq_exp, ← Complex.exp_neg]
  set t : ℝ := 2 * Real.pi * (k.val : ℝ) / 8
  have h3 : -((t : ℂ) * Complex.I) = ((-t : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [h3, Complex.exp_mul_I, Complex.exp_mul_I]
  push_cast
  simp [Complex.cos_neg, Complex.sin_neg]
  ring

/-- Every Hückel eigenvalue `2 cos (2πk/8)` of `C₈` is realized by an explicit eigenvector. -/
