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

namespace Math

/-- No sum of two squares is congruent to `3` mod `4`. -/

theorem sum_two_squares {p : ℕ} (hp : Nat.Prime p) :
    (∃ a b : ℕ, a ^ 2 + b ^ 2 = p) ↔ (p = 2 ∨ p % 4 = 1) := by
  constructor
  · rintro ⟨a, b, rfl⟩
    rcases hp.eq_two_or_odd with h | h
    · exact Or.inl h
    · have := sq_add_sq_mod_four_ne_three a b
      omega
  · rintro (rfl | h)
    · exact ⟨1, 1, by norm_num⟩
    · haveI : Fact (Nat.Prime p) := ⟨hp⟩
      exact Nat.Prime.sq_add_sq (by omega)

end Math

#print axioms Math.sum_two_squares

