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

lemma card_redN_add_card_blueN (v : Fin 9) : (redN c v).card + (blueN c v).card = 8 := by
  have hb : blueN c v = (Finset.univ.erase v).filter (fun u => ¬ (c v u = true)) := by
    simp [blueN, Bool.not_eq_true]
  rw [hb, redN, Finset.card_filter_add_card_filter_not]
  simp

/-- With no `true` triangle, the `true`-neighbourhood of a vertex is `false`-monochromatic. -/
