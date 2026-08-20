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

theorem pathGraph_dist_eq {n : ℕ} (u v : Fin n) :
    (pathGraph n).dist u v = Nat.dist u.val v.val := by
  refine le_antisymm (pathGraph_dist_le u v) ?_
  obtain ⟨p, hp⟩ := (SimpleGraph.pathGraph_preconnected n u v).exists_walk_length_eq_dist
  rw [← hp]
  exact pathGraph_le_length_of_walk p

/-- Sum of `n - i` over `i < n` is `C(n+1, 2)`. -/
