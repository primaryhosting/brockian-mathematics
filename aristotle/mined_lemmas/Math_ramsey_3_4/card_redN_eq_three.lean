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

lemma card_redN_eq_three (hsymm : ∀ x y, c x y = c y x)
    (hR : ∀ T : Finset (Fin 9), T.card = 3 → ¬ MonoClique c true T)
    (hB : ∀ T : Finset (Fin 9), T.card = 4 → ¬ MonoClique c false T) (v : Fin 9) :
    (redN c v).card = 3 := by
  have h1 := card_redN_add_card_blueN (c := c) v
  have h2 := card_redN_le hsymm hR hB v
  have h3 := card_blueN_le hsymm hR hB v
  omega

/-- The parity obstruction: a graph on 9 vertices cannot be 3-regular. -/
