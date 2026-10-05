/-
# Wiener Path Formula
Category: Chemistry
Target: Chem.wiener_path_formula
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Finset SimpleGraph

namespace Chem

/-- The Wiener index of a graph on a linearly ordered finite vertex set: the sum of the
graph distances over all unordered pairs of distinct vertices. -/

lemma sum_range_sub (n : ℕ) : ∑ a ∈ Finset.range n, (n - a) = (n + 1).choose 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have : ∑ a ∈ Finset.range n, (n + 1 - a) = (∑ a ∈ Finset.range n, (n - a)) + n := by
        rw [show ∑ a ∈ Finset.range n, (n + 1 - a)
              = ∑ a ∈ Finset.range n, ((n - a) + 1) from
            Finset.sum_congr rfl (fun a ha => by
              simp only [Finset.mem_range] at ha; omega)]
        rw [Finset.sum_add_distrib]
        simp
      rw [this, ih]
      rw [Nat.choose_succ_succ' (n + 1) 1]
      simp [Nat.choose_one_right]
      omega

/-- The double sum computing the Wiener index of the path graph. -/
