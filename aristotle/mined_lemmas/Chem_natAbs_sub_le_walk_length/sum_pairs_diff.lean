/-
# Wiener Path Formula
Category: Chemistry
Target: Chem.wiener_path_formula
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators

namespace Chem

open SimpleGraph Finset

/-- The Wiener index of a finite graph whose vertices carry a linear order:
the sum of the graph distances over all unordered pairs of distinct vertices
(each pair `{u, v}` counted once, via `u < v`). -/

lemma sum_pairs_diff (n : ℕ) :
    ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, (if i < j then j - i else 0)
      = (n + 1).choose 3 := by
  induction n with
  | zero => simp [Nat.choose]
  | succ n ih =>
    have inner : ∀ i ∈ Finset.range (n + 1),
        (∑ j ∈ Finset.range (n + 1), (if i < j then j - i else 0))
          = (∑ j ∈ Finset.range n, (if i < j then j - i else 0))
            + (if i < n then n - i else 0) := by
      intro i _; rw [Finset.sum_range_succ]
    rw [Finset.sum_congr rfl inner, Finset.sum_add_distrib, Finset.sum_range_succ
      (fun i => ∑ j ∈ Finset.range n, (if i < j then j - i else 0)),
      Finset.sum_range_succ (fun i => if i < n then n - i else 0), ih]
    have h1 : (∑ j ∈ Finset.range n, (if n < j then j - n else 0)) = 0 := by
      apply Finset.sum_eq_zero; intro j hj; simp at hj; simp; omega
    have h2 : (∑ i ∈ Finset.range n, (if i < n then n - i else 0))
        = ∑ i ∈ Finset.range n, (n - i) := by
      apply Finset.sum_congr rfl; intro i hi; simp at hi; simp [hi]
    rw [h1, h2, sum_range_sub_nat]
    simp [Nat.choose_succ_succ (n + 1) 2]
    omega

/-- **Wiener index of the path graph**: the Wiener index of `P_n` equals `C(n+1, 3)`. -/
