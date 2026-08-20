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

namespace Brockian

/-- The new wheel modulus `1327` is prime. -/

theorem GoldbachWheelK2_1327_nat (r : ℕ) (hr : r < 1327) :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ (p + q) % 1327 = r := by
  obtain ⟨p, q, -, -, hp, hq, hpq⟩ := GoldbachWheelK2_1327 (r : ZMod 1327) 0
  refine ⟨p, q, hp, hq, ?_⟩
  have h : ((p + q : ℕ) : ZMod 1327) = ((r : ℕ) : ZMod 1327) := by push_cast [hpq]; ring
  have := (ZMod.natCast_eq_natCast_iff _ _ _).mp h
  simpa [Nat.ModEq, Nat.mod_eq_of_lt hr] using this

end Brockian

