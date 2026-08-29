import Mathlib
/-!
# Wiener Path Formula
Category: Chemistry
Target: Chem.wiener_path_formula
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset SimpleGraph

namespace Chem

/-- The Wiener index of a finite graph: the sum of the distances between all
unordered pairs of vertices.  It is computed here as half of the sum over all
ordered pairs. -/

lemma sum_natDist_range (n : ℕ) :
    ∑ i ∈ range n, Nat.dist i n = (n + 1).choose 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have h : ∀ i ∈ range n, Nat.dist i (n + 1) = Nat.dist i n + 1 := by
      intro i hi
      simp only [Finset.mem_range] at hi
      simp only [Nat.dist]
      omega
    rw [Finset.sum_congr rfl h, Finset.sum_add_distrib, ih]
    simp [Nat.dist, Nat.choose_succ_succ (n + 1) 1]
    ring

/-- The doubled Wiener sum of the path on `n` vertices. -/
