import Mathlib

/-!
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Real Matrix Finset

/-- A primitive 18-th root of unity. -/

lemma ee_add_neg (k : ZMod 18) :
    ee k + ee (-k) = ((2 * Real.cos (2 * Real.pi * k.val / 18) : ℝ) : ℂ) := by
  set t : ℝ := 2 * Real.pi * k.val / 18 with ht
  have h1 : ee k = Complex.exp ((t : ℂ) * Complex.I) := om_pow_nat k.val
  have hmul : ee k * ee (-k) = 1 := by rw [← ee_add, add_neg_cancel, ee_zero]
  have h2 : ee (-k) = Complex.exp (-((t : ℂ) * Complex.I)) := by
    have hne : ee k ≠ 0 := ee_ne_zero k
    field_simp [h1, Complex.exp_neg] at hmul ⊢
    rw [← hmul, h1]
  rw [h1, h2]
  have := Complex.cos_eq_exp_add_exp_neg_div_two ((t : ℂ))
  push_cast
  rw [← Complex.ofReal_cos]
  push_cast
  rw [this]
  ring

/-- Adjacency matrix of the cycle graph `C₁₈`, with vertices indexed by `ZMod 18`. -/
