import Mathlib
/-!
# Ramsey 3 4
Category: Pure Mathematics
Target: Math.ramsey_3_4
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

namespace Math

/-- `MonoClique c b T` says that all pairs of distinct vertices of `T` get colour `b`
under the (edge-)colouring `c`. -/

theorem not_hasRamsey34_eight : ¬ HasRamsey34 8 := by
  intro h
  rcases h wagner wagner_symm with ⟨T, hT, hm⟩ | ⟨T, hT, hm⟩
  · exact wagner_no_triangle T hT hm
  · exact wagner_no_indep_four T hT hm

