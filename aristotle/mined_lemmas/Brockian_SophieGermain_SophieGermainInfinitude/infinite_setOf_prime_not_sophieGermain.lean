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

theorem infinite_setOf_prime_not_sophieGermain :
    {p : ℕ | p.Prime ∧ ¬ IsSophieGermain p}.Infinite := by
  have h := Nat.infinite_setOf_prime_modEq_one (k := 3) (by norm_num)
  refine h.mono ?_
  rintro p ⟨hp, hmod⟩
  exact ⟨hp, not_isSophieGermain_of_modEq_one_mod_three hp hmod⟩

end Brockian.SophieGermain

