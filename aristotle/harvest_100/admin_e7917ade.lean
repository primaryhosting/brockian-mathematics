/-!
# Sum Two Squares
Category: Pure Mathematics
Target: Math.sum_two_squares
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Math

/-- A square is congruent to `0` or `1` modulo `4`. -/
lemma sq_mod_four (a : ℕ) : a ^ 2 % 4 = 0 ∨ a ^ 2 % 4 = 1 := by
  have h : a ^ 2 % 4 = (a % 4) ^ 2 % 4 := by
    rw [Nat.pow_mod]
  have h4 : a % 4 < 4 := Nat.mod_lt _ (by norm_num)
  interval_cases h' : (a % 4) <;> simp [h, h'] at h ⊢ <;> omega

/-- A sum of two squares is never congruent to `3` modulo `4`. -/
lemma sum_sq_mod_four_ne_three (a b : ℕ) : (a ^ 2 + b ^ 2) % 4 ≠ 3 := by
  have ha := sq_mod_four a
  have hb := sq_mod_four b
  omega

/-- **Fermat's two-square theorem** (prime case): a prime `p` is a sum of two squares
iff `p = 2` or `p ≡ 1 (mod 4)`. -/
theorem sum_two_squares {p : ℕ} (hp : p.Prime) :
    (∃ a b : ℕ, p = a ^ 2 + b ^ 2) ↔ (p = 2 ∨ p % 4 = 1) := by
  constructor
  · rintro ⟨a, b, rfl⟩
    rcases hp.eq_two_or_odd with h | h
    · exact Or.inl h
    · have := sum_sq_mod_four_ne_three a b
      omega
  · intro h
    rcases h with rfl | h
    · exact ⟨1, 1, by norm_num⟩
    · haveI : Fact p.Prime := ⟨hp⟩
      obtain ⟨a, b, hab⟩ := Nat.Prime.sq_add_sq (p := p) (by omega)
      exact ⟨a, b, hab.symm⟩

end Math

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

