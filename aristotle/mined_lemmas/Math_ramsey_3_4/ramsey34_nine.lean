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

theorem ramsey34_nine : HasRamsey34 9 := by
  intro c hsymm
  by_contra hcon
  push_neg at hcon
  obtain ⟨h3, h4⟩ := hcon
  exact not_three_regular hsymm (card_redN_eq_three hsymm h3 h4)

end Nine

/-- The Wagner graph (Möbius ladder) on `ℤ/8`: `i ~ j` iff `i - j ∈ {1, 4, 7}`. -/
