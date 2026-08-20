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

theorem five_color_theorem {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hdeg : ∀ (t : Finset V) (H : SimpleGraph V), Reduces Finset.univ G t H →
      t.Nonempty → ∃ v ∈ t, (nbrs t H v).card ≤ 5)
    (hK6 : ∀ (t : Finset V) (H : SimpleGraph V), Reduces Finset.univ G t H → NoK6 t H) :
    G.Colorable 5 :=
  five_color_theorem_of_reducible G fun t H hred =>
    lowDegreeVertex_of_minDegree_le_five (hdeg t H hred) (hK6 t H hred)

/-- Reductions only shrink the vertex set. -/
