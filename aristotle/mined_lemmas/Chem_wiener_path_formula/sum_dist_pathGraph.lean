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

theorem sum_dist_pathGraph (n : ℕ) :
    ∑ i ∈ range n, ∑ j ∈ range n, (i - j + (j - i)) = 2 * (n + 1).choose 3 := by
  induction n with
  | zero => simp [Nat.choose]
  | succ n ih =>
    have hinner : ∀ i ∈ range (n + 1),
        ∑ j ∈ range (n + 1), (i - j + (j - i)) =
          (∑ j ∈ range n, (i - j + (j - i))) + (i - n + (n - i)) := by
      intro i _
      rw [Finset.sum_range_succ]
    rw [Finset.sum_congr rfl hinner, Finset.sum_add_distrib, Finset.sum_range_succ
      (fun i => ∑ j ∈ range n, (i - j + (j - i)))]
    have h1 : ∑ j ∈ range n, (n - j + (j - n)) = ∑ j ∈ range n, (n - j) := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      simp only [Finset.mem_range] at hj
      omega
    have h2 : ∑ i ∈ range (n + 1), (i - n + (n - i)) = ∑ i ∈ range n, (n - i) := by
      rw [Finset.sum_range_succ]
      have : ∑ i ∈ range n, (i - n + (n - i)) = ∑ i ∈ range n, (n - i) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        simp only [Finset.mem_range] at hi
        omega
      omega
    rw [h1, h2, ih]
    have hg := two_mul_sum_gap n
    have hc : (n + 1 + 1).choose 3 = (n + 1).choose 3 + (n + 1).choose 2 := by
      rw [show (3 : ℕ) = 2 + 1 from rfl, Nat.choose_succ_succ' (n + 1) 2, Nat.add_comm]
    have hc2 := two_mul_choose_two n
    omega

/-- **The Wiener index of the path graph `P n` is `C(n+1, 3)`.** -/
