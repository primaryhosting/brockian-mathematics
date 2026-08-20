import Mathlib

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

import Mathlib

/-!
# Sophie Germain Infinitude
Category: Brockian Conjecture
Target: Brockian.SophieGermain.SophieGermainInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.SophieGermain

/-- `p` is a *Sophie Germain prime* if both `p` and `2 * p + 1` are prime. -/

theorem infinite_sophieGermainSet_iff_unbounded :
    sophieGermainSet.Infinite ↔ ∀ N : ℕ, ∃ p, N < p ∧ IsSophieGermain p := by
  constructor
  · intro h N
    obtain ⟨p, hp, hlt⟩ := h.exists_gt N
    exact ⟨p, hlt, hp⟩
  · intro h
    exact Set.infinite_of_forall_exists_gt (fun N => by
      obtain ⟨p, hlt, hp⟩ := h N
      exact ⟨p, hp, hlt⟩)

/-! ## Dickson's conjecture -/

/-- A finite family of linear forms `x ↦ aᵢ * x + bᵢ` (encoded as pairs `(aᵢ, bᵢ)`) is
*admissible* if for every prime `q` there is some `n` at which no form is divisible by `q`. -/
