/-
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
  have h : a % 2 = 0 ∨ a % 2 = 1 := Nat.mod_two_eq_zero_or_one a
  obtain ⟨k, hk⟩ : ∃ k, a = 2 * k ∨ a = 2 * k + 1 := by
    refine ⟨a / 2, ?_⟩
    rcases h with h | h
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  rcases hk with rfl | rfl
  · left; have : (2 * k) ^ 2 = 4 * k ^ 2 := by ring
    omega
  · right
    have : (2 * k + 1) ^ 2 = 4 * (k ^ 2 + k) + 1 := by ring
    omega

/-- If an odd number is a sum of two squares, it is congruent to `1` modulo `4`. -/
lemma mod_four_eq_one_of_odd_sq_add_sq {n a b : ℕ} (hodd : n % 2 = 1)
    (h : a ^ 2 + b ^ 2 = n) : n % 4 = 1 := by
  rcases sq_mod_four a with ha | ha <;> rcases sq_mod_four b with hb | hb <;> omega

/-- **Fermat's two–squares theorem.** A prime `p` is a sum of two squares if and only if
`p = 2` or `p ≡ 1 (mod 4)`. -/
theorem sum_two_squares (p : ℕ) (hp : p.Prime) :
    (∃ a b : ℕ, a ^ 2 + b ^ 2 = p) ↔ (p = 2 ∨ p % 4 = 1) := by
  constructor
  · rintro ⟨a, b, hab⟩
    by_cases h2 : p = 2
    · exact Or.inl h2
    · exact Or.inr (mod_four_eq_one_of_odd_sq_add_sq
        (Nat.odd_iff.mp (hp.odd_of_ne_two h2)) hab)
  · rintro (rfl | h)
    · exact ⟨1, 1, by norm_num⟩
    · haveI : Fact p.Prime := ⟨hp⟩
      exact Nat.Prime.sq_add_sq (by omega)

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

