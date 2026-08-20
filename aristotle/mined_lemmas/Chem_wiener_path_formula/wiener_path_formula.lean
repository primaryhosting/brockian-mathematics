/-
# Wiener Path Formula
Category: Chemistry
Target: Chem.wiener_path_formula
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Wiener Path Formula
Category: Chemistry
Target: Chem.wiener_path_formula
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Chem

open SimpleGraph Finset

/-- The Wiener index of a finite graph: the sum of the distances between all
unordered pairs of vertices, i.e. half the sum of `dist u v` over all ordered pairs. -/

theorem wiener_path_formula (n : ℕ) :
    wienerIndex (SimpleGraph.pathGraph n) = Nat.choose (n + 1) 3 := by
  have hsum : ∑ u : Fin n, ∑ v : Fin n, (pathGraph n).dist u v = 2 * Nat.choose (n + 1) 3 := by
    have hinner : ∀ u : Fin n, ∑ v : Fin n, (pathGraph n).dist u v
        = ∑ j ∈ Finset.range n, Nat.dist u.val j := by
      intro u
      rw [← Fin.sum_univ_eq_sum_range (fun j => Nat.dist u.val j) n]
      exact Finset.sum_congr rfl fun v _ => pathGraph_dist_eq u v
    rw [Finset.sum_congr rfl fun u _ => hinner u,
      Fin.sum_univ_eq_sum_range (fun i => ∑ j ∈ Finset.range n, Nat.dist i j) n,
      sum_nat_dist_range n]
  unfold wienerIndex
  rw [hsum]
  omega

end Chem

