import Mathlib

/-!
# Wiener Path Formula
Category: Chemistry
Target: Chem.wiener_path_formula
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open SimpleGraph Finset

namespace Chem

/-- The Wiener index of a finite graph: the sum of the distances `d(u,v)` over all
unordered pairs `{u, v}` of vertices (the diagonal pairs contribute `0`). -/

theorem sum_range_pairs (n : ℕ) :
    ∑ i ∈ range n, ∑ j ∈ range n, (if i < j then j - i else 0) = (n + 1).choose 3 := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have h2 : ∀ i ∈ range n, ∑ j ∈ range (n + 1), (if i < j then j - i else 0)
        = (∑ j ∈ range n, (if i < j then j - i else 0)) + (n - i) := by
      intro i hi
      rw [Finset.sum_range_succ]
      simp only [Finset.mem_range] at hi
      simp [hi]
    rw [Finset.sum_congr rfl h2, Finset.sum_add_distrib, ih, sum_range_sub]
    have h3 : ∑ j ∈ range (n + 1), (if n < j then j - n else 0) = 0 := by
      refine Finset.sum_eq_zero (fun j hj => ?_)
      simp only [Finset.mem_range] at hj
      simp only [ite_eq_right_iff]
      omega
    have h : (n + 1 + 1).choose 3 = (n + 1).choose 2 + (n + 1).choose 3 :=
      Nat.choose_succ_succ (n + 1) 2
    rw [h3, add_zero]
    omega

/-! ### The Wiener index of the path graph -/

/-- **Wiener path formula**: the Wiener index of the path graph `P n` on `n` vertices
equals `C(n + 1, 3)`. -/
