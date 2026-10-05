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

lemma sum_sum_natDist (n : ℕ) :
    ∑ i ∈ range n, ∑ j ∈ range n, Nat.dist i j = 2 * (n + 1).choose 3 := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have h1 : ∀ i ∈ range n, ∑ j ∈ range (n + 1), Nat.dist i j
        = (∑ j ∈ range n, Nat.dist i j) + Nat.dist i n := fun i _ => Finset.sum_range_succ _ _
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, ih, Finset.sum_range_succ]
    have h2 : ∑ j ∈ range n, Nat.dist n j = ∑ j ∈ range n, Nat.dist j n :=
      Finset.sum_congr rfl fun j _ => Nat.dist_comm _ _
    rw [h2, sum_natDist_range n]
    have h3 : (n + 2).choose 3 = (n + 1).choose 2 + (n + 1).choose 3 := Nat.choose_succ_succ (n + 1) 2
    simp [Nat.dist_self, h3]
    ring

/-- **Wiener path formula**: the Wiener index of the path graph `P n` equals
`C(n+1, 3)`. -/
