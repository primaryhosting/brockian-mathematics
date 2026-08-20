import Mathlib

/-!
# Ramsey 3 5
Category: Pure Mathematics
Target: Math.ramsey_3_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Ramsey

/-- A `b`-monochromatic set of vertices for the edge colouring `c`. -/

lemma ramsey_34 {c : ℕ → ℕ → Bool} (hsym : ∀ x y, c x y = c y x) {s : Finset ℕ}
    (hcard : 9 ≤ s.card) : Arrows c s 3 4 := by
  obtain ⟨t, hts, hc⟩ := Finset.exists_subset_card_eq hcard
  exact Arrows.of_subset hts (ramsey_34_card hsym hc)

/-- `R(3,5) ≤ 14`. -/
