import Mathlib

/-!
# Deutsch Jozsa
Category: Frontier Qi
Target: QI.deutsch_jozsa
Statement: Deutsch–Jozsa decides constant-vs-balanced with one query.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QI

open Finset

/-- The sign `(-1)^b` attached to a boolean. -/

theorem phase_orthogonality {n : ℕ} (x x' : Fin n → Bool) :
    ∑ y, phase x y * phase x' y = if x = x' then (2 : ℝ) ^ n else 0 := by
  have key : ∀ y : Fin n → Bool, phase x y * phase x' y
      = ∏ i, ((if x i && y i then (-1 : ℝ) else 1) * (if x' i && y i then (-1 : ℝ) else 1)) := by
    intro y; rw [phase, phase, ← Finset.prod_mul_distrib]
  simp_rw [key]
  rw [show (∑ y : Fin n → Bool, ∏ i,
        ((if x i && y i then (-1 : ℝ) else 1) * (if x' i && y i then (-1 : ℝ) else 1)))
      = ∏ i, ∑ b : Bool,
        ((if x i && b then (-1 : ℝ) else 1) * (if x' i && b then (-1 : ℝ) else 1)) by
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]]
  have hb : ∀ i, (∑ b : Bool,
      ((if x i && b then (-1 : ℝ) else 1) * (if x' i && b then (-1 : ℝ) else 1)))
      = if x i = x' i then (2 : ℝ) else 0 := by
    intro i
    rw [Fintype.sum_bool]
    cases hx : x i <;> cases hx' : x' i <;> norm_num
  simp_rw [hb]
  by_cases h : x = x'
  · subst h; simp
  · rw [if_neg h]
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ x' i := by
      by_contra hc; push_neg at hc; exact h (funext hc)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [if_neg hi])

