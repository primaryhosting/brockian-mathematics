/-
# Ramsey 3 4
Category: Pure Mathematics
Target: Math.ramsey_3_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Math

open Finset SimpleGraph

/-- The Ramsey property `R(3,4) ≤ n`: every simple graph on `n` vertices contains either a
triangle or an independent set of size `4`. -/

def RamseyProp34 (n : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n),
    (∃ s : Finset (Fin n), G.IsNClique 3 s) ∨ (∃ t : Finset (Fin n), G.IsNIndepSet 4 t)

/-! ### The Ramsey bound `R(3,3) ≤ 6` in the form we need -/

/-- Among any six vertices of a graph there are three that are pairwise adjacent or three that
are pairwise non-adjacent (i.e. `R(3,3) ≤ 6`). -/
