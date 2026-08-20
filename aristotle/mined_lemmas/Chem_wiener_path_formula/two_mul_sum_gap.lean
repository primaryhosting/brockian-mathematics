import Mathlib

/-!
# Wiener Path Formula
Category: Chemistry
Target: Chem.wiener_path_formula
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Finset SimpleGraph

/-- The Wiener index of a finite graph: the sum of the distances over all unordered
pairs of vertices. -/

lemma two_mul_sum_gap (n : ℕ) : 2 * ∑ i ∈ range n, (n - i) = n * (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have h : ∑ i ∈ range n, (n + 1 - i) = ∑ i ∈ range n, ((n - i) + 1) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      simp only [Finset.mem_range] at hi
      omega
    rw [h, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range]
    have hr : (n + 1) * (n + 1 + 1) = n * (n + 1) + 2 * (n + 1) := by ring
    simp only [smul_eq_mul, mul_one]
    omega

/-- `2 * C(n+1, 2) = n * (n+1)`. -/
