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

def IsProperColoring (s : Finset V) (G : SimpleGraph V) (c : V → Fin 5) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, G.Adj x y → c x ≠ c y

/-- `G` restricted to the vertex set `s` is `5`-colourable. -/
