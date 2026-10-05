import Mathlib

/-!
# Huckel C 9
Category: Chemistry
Target: Chem.huckel_C9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Matrix Finset

noncomputable section

/-- A primitive 9-th root of unity. -/

lemma ee_add_ee_neg (k : ZMod 9) : ee k + ee (-k) = eig k := by
  have hmul : ee k * ee (-k) = 1 := by rw [← ee_add, add_neg_cancel, ee_zero]
  have hne : ee k ≠ 0 := by
    intro h; rw [h, zero_mul] at hmul; exact zero_ne_one hmul
  have hinv : ee (-k) = (ee k)⁻¹ := by
    field_simp at hmul ⊢
    linear_combination hmul
  rw [hinv, ee_eq_exp, ← Complex.exp_neg]
  rw [show -((2 * Real.pi * (k.val : ℝ) / 9 : ℝ) * Complex.I)
      = ((-(2 * Real.pi * k.val / 9) : ℝ)) * Complex.I by push_cast; ring]
  rw [Complex.exp_mul_I, Complex.exp_mul_I, eig]
  push_cast
  rw [Complex.cos_neg, Complex.sin_neg]
  ring

/-! ### The adjacency matrix acts by shifts -/

