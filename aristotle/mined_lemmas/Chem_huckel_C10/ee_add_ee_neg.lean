import Mathlib

/-!
# Huckel C 10
Category: Chemistry
Target: Chem.huckel_C10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real

set_option maxHeartbeats 1000000

namespace Chem

/-- The adjacency matrix of the cycle graph `C₁₀`, with vertices indexed by `ZMod 10`:
`i` and `j` are adjacent iff they differ by `1` modulo `10`. -/

lemma ee_add_ee_neg (m : ZMod 10) :
    ee m + ee (-m) = ((2 * Real.cos (2 * Real.pi * m.val / 10) : ℝ) : ℂ) := by
  set t : ℝ := 2 * Real.pi * m.val / 10 with ht
  have h1 : ee m = Complex.exp ((t : ℂ) * Complex.I) := ee_eq_exp m
  have hmul : ee m * ee (-m) = 1 := by rw [← ee_add]; simp [ee_zero]
  have hne : ee m ≠ 0 := by rw [h1]; exact Complex.exp_ne_zero _
  have h2 : ee (-m) = Complex.exp (-((t : ℂ) * Complex.I)) := by
    rw [Complex.exp_neg, ← h1]
    exact Eq.symm (DivisionMonoid.inv_eq_of_mul (ee m) (ee (-m)) hmul)
  rw [h1, h2, Complex.exp_mul_I, neg_mul_eq_neg_mul, Complex.exp_mul_I]
  push_cast
  simp [Complex.cos_neg, Complex.sin_neg]
  ring

