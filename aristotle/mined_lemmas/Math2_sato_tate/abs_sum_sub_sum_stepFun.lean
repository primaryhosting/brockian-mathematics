/-
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Topology Set MeasureTheory intervalIntegral
open scoped Real

namespace Math2

/-- The Sato–Tate density on `[0, π]`: `θ ↦ (2/π) sin²θ`. -/

lemma abs_sum_sub_sum_stepFun {f : ℝ → ℝ} {n : ℕ} (hn : 0 < n) {θ : ℕ → ℝ}
    (hrange : ∀ p, θ p ∈ Icc 0 Real.pi) {c : ℝ}
    (hunif : ∀ x ∈ Icc 0 Real.pi, ∀ y ∈ Icc 0 Real.pi, |x - y| ≤ Real.pi / n → |f x - f y| ≤ c)
    (X : ℕ) :
    |(∑ p ∈ primesBelow X, f (θ p)) - ∑ p ∈ primesBelow X, stepFun f n (θ p)|
      ≤ ((primesBelow X).card : ℝ) * c := by
  rw [← Finset.sum_sub_distrib]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hterm : ∀ p ∈ primesBelow X, |f (θ p) - stepFun f n (θ p)| ≤ c := by
    intro p _
    obtain ⟨k, hk, habs, heq⟩ := stepFun_eq f hn (hrange p)
    rw [heq]
    exact hunif _ (hrange p) _ (grid_mem hn hk) habs
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_const, nsmul_eq_mul]

/-- The interval form of Sato–Tate equidistribution implies the test-function form. -/
