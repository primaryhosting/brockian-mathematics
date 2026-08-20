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

theorem wagner_compl_cliqueFree4 : wagnerᶜ.CliqueFree 4 := by
  intro t
  revert t
  decide

