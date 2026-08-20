/-
# Entropy Concave
Category: Chemistry
Target: Chem.entropy_concave
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Real Finset

/-- The Gibbs entropy of a (finite) probability vector `p`: `S(p) = -∑ i, p i * log (p i)`,
written using Mathlib's `Real.negMulLog x = -x * log x` (so that the `p i = 0` terms vanish). -/

theorem entropy_strictConcave (n : ℕ) :
    StrictConcaveOn ℝ {p : Fin n → ℝ | ∀ i, 0 ≤ p i} entropy := by
  refine ⟨(entropy_concave n).1, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  obtain ⟨j, hj⟩ : ∃ j, x j ≠ y j := Function.ne_iff.1 hxy
  simp only [entropy, smul_eq_mul, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_lt_sum (fun i _ => Real.concaveOn_negMulLog.2 (hx i) (hy i) ha.le hb.le hab)
    ⟨j, Finset.mem_univ j, Real.strictConcaveOn_negMulLog.2 (hx j) (hy j) hj ha hb hab⟩

/-- Concavity of the Gibbs entropy restricted to the probability simplex. -/
