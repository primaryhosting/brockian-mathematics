import Mathlib

/-!
# Wiener Path Formula
Category: Chemistry
Target: Chem.wiener_path_formula
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Finset SimpleGraph

namespace Chem

/-- The Wiener index of a finite graph: the sum of the graph distances over all unordered
pairs of vertices.  It is computed here as half of the sum of `G.dist u v` over all ordered
pairs `(u, v)`. -/

theorem double_sum_natDist (n : ℕ) :
    ∑ i ∈ range n, ∑ j ∈ range n, Nat.dist i j = 2 * Nat.choose (n + 1) 3 := by
  induction n with
  | zero => decide
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have h1 : ∀ i ∈ range n, ∑ j ∈ range (n + 1), Nat.dist i j
          = (∑ j ∈ range n, Nat.dist i j) + Nat.dist i n := fun i _ => Finset.sum_range_succ _ _
      have h2 : ∑ j ∈ range n, Nat.dist n j = ∑ j ∈ range n, Nat.dist j n :=
        Finset.sum_congr rfl fun j _ => Nat.dist_comm n j
      rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, ih, sum_natDist_top,
        Finset.sum_range_succ, Nat.dist_self, add_zero, h2, sum_natDist_top]
      have hc3 : Nat.choose (n + 1 + 1) 3 = Nat.choose (n + 1) 2 + Nat.choose (n + 1) 3 := rfl
      omega

/-! ### The Wiener index of a path -/

/-- **Wiener path formula**: the Wiener index of the path graph `P n` equals `C(n+1, 3)`. -/
