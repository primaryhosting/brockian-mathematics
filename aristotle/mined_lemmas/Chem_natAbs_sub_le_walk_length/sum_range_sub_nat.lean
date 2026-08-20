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

lemma sum_range_sub_nat (n : ℕ) : ∑ i ∈ Finset.range n, (n - i) = (n + 1).choose 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have h : ∀ i ∈ Finset.range n, (n + 1 - i) = (n - i) + 1 := by
      intro i hi; simp at hi; omega
    rw [Finset.sum_congr rfl h, Finset.sum_add_distrib, ih]
    simp [Nat.choose_succ_succ (n + 1) 1, Nat.choose_one_right]
    omega

