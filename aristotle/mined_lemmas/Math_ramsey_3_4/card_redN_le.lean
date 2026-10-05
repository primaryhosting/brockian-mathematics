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

lemma card_redN_le (hsymm : ∀ x y, c x y = c y x)
    (hR : ∀ T : Finset (Fin 9), T.card = 3 → ¬ MonoClique c true T)
    (hB : ∀ T : Finset (Fin 9), T.card = 4 → ¬ MonoClique c false T) (v : Fin 9) :
    (redN c v).card ≤ 3 := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨S, hS, hcard⟩ :=
    Finset.exists_subset_card_eq (s := redN c v) (n := 4) (by omega)
  exact hB S hcard ((redN_mono_false hsymm hR v).subset hS)

