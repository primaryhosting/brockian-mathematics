import Mathlib

/-!
# Five Color Theorem
Category: Frontier — Fields Medal Work
Target: Frontier.five_color_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Frontier

variable {V : Type*} [DecidableEq V]

/-- The neighbours of `v` inside the vertex set `s`. -/

lemma nbrs_subset (s : Finset V) (G : SimpleGraph V) (v : V) : nbrs s G v ⊆ s.erase v :=
  Finset.filter_subset _ _

/-- Identify the vertex `w` with the vertex `u`: every neighbour of `w` becomes a neighbour
of `u`.  (Used with `u` and `w` two non-adjacent neighbours of a degree-5 vertex, in which
case this is precisely the contraction of the two edges `vu` and `vw`.) -/
