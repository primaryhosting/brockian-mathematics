import Mathlib

/-!
# Sum Two Squares
Category: Pure Mathematics
Target: Math.sum_two_squares
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

namespace Math

/-- Every square is `0` or `1` modulo `4`. -/
theorem sq_mod_four (a : ℕ) : a ^ 2 % 4 = 0 ∨ a ^ 2 % 4 = 1 := by
  rcases Nat.even_or_odd a with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · left; ring_nf; omega
  · right; ring_nf; omega

/-- **Fermat's two-square theorem**: a prime `p` is a sum of two squares
if and only if `p = 2` or `p ≡ 1 (mod 4)`. -/
theorem sum_two_squares (p : ℕ) (hp : Nat.Prime p) :
    (∃ a b : ℕ, a ^ 2 + b ^ 2 = p) ↔ (p = 2 ∨ p % 4 = 1) := by
  constructor
  · rintro ⟨a, b, rfl⟩
    rcases hp.eq_two_or_odd with h | h
    · exact Or.inl h
    · right
      have h4 : (a ^ 2 + b ^ 2) % 4 = (a ^ 2 % 4 + b ^ 2 % 4) % 4 := Nat.add_mod _ _ _
      rcases sq_mod_four a with ha | ha <;> rcases sq_mod_four b with hb | hb <;> omega
  · intro h
    haveI : Fact (Nat.Prime p) := ⟨hp⟩
    exact Nat.Prime.sq_add_sq (by omega)

end Math

