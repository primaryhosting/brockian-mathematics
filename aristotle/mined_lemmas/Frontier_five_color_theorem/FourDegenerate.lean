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

def FourDegenerate (s : Finset V) (G : SimpleGraph V) : Prop :=
  ∀ t ⊆ s, t.Nonempty → ∃ v ∈ t, (nbrs t G v).card ≤ 4

/-- The greedy half of the five colour theorem: a `4`-degenerate graph is `5`-colourable. -/
