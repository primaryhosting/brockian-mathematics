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

theorem five_color_theorem_of_reducible {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (h : FiveColorReducible (Finset.univ : Finset V) G) : G.Colorable 5 := by
  obtain ⟨c, hc⟩ := fiveColorable_of_reducible (Fintype.card V) Finset.univ G
    (le_of_eq (Finset.card_univ)) h
  refine ⟨SimpleGraph.Coloring.mk c ?_⟩
  intro a b hab
  exact hc a (Finset.mem_univ a) b (Finset.mem_univ b) hab

/-- The vertex set `s` carries no `K₆`: among any six of its vertices, two are non-adjacent.
A planar graph has this property, since `K₆` contains `K₅`, which is not planar. -/
