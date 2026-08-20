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

def NoK6 (s : Finset V) (G : SimpleGraph V) : Prop :=
  ∀ K : Finset V, K ⊆ s → K.card = 6 → ∃ x ∈ K, ∃ y ∈ K, x ≠ y ∧ ¬ G.Adj x y

/-- A vertex of degree at most `5` (which Euler's formula provides for planar graphs)
together with the absence of a `K₆` gives the local condition `LowDegreeVertex`. -/
