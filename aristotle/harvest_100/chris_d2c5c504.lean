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

/-- Squares are `0` or `1` mod `4`. -/
lemma sq_mod_four (a : ℕ) : a ^ 2 % 4 = 0 ∨ a ^ 2 % 4 = 1 := by
  have h : a % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have ha : a ^ 2 % 4 = (a % 4) ^ 2 % 4 := by
    rw [Nat.pow_mod]
  interval_cases h' : (a % 4) <;> simp [ha]

/-- **Fermat's two-square theorem**: a prime `p` is a sum of two squares
iff `p = 2` or `p ≡ 1 (mod 4)`. -/
theorem sum_two_squares {p : ℕ} (hp : p.Prime) :
    (∃ a b : ℕ, p = a ^ 2 + b ^ 2) ↔ (p = 2 ∨ p % 4 = 1) := by
  constructor
  · rintro ⟨a, b, hab⟩
    rcases eq_or_ne p 2 with h2 | h2
    · exact Or.inl h2
    · right
      have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two h2)
      have hmod : p % 4 = (a ^ 2 % 4 + b ^ 2 % 4) % 4 := by
        rw [hab, Nat.add_mod]
      rcases sq_mod_four a with ha | ha <;> rcases sq_mod_four b with hb | hb <;>
        omega
  · rintro (rfl | h1)
    · exact ⟨1, 1, by norm_num⟩
    · haveI : Fact p.Prime := ⟨hp⟩
      obtain ⟨a, b, hab⟩ := Nat.Prime.sq_add_sq (p := p) (by omega)
      exact ⟨a, b, hab.symm⟩

end Math
#print axioms Math.sum_two_squares

