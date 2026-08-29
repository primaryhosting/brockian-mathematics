import Mathlib
/-!
# Sunflower Bound
Category: Frontier Math
Target: Math2.sunflower_bound
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Math2

variable {α : Type*} [DecidableEq α]

/-- A family `S` of finite sets is a *sunflower with core `K`* if any two distinct members
of `S` meet exactly in `K`. -/

theorem card_le_of_no_sunflower {w r : ℕ} (F : Finset (Finset α)) (hF : ∀ A ∈ F, A.card = w)
    (hno : ¬ ∃ S ⊆ F, ∃ K : Finset α, S.card = r ∧ IsSunflower S K) :
    F.card ≤ Nat.factorial w * (r - 1) ^ w := by
  by_contra h
  exact hno (sunflower_bound F hF (by omega))

end Math2

