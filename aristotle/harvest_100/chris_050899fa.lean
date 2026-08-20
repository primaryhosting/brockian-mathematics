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
lemma sq_mod_four (n : ℕ) : n ^ 2 % 4 = 0 ∨ n ^ 2 % 4 = 1 := by
  have h : n ^ 2 % 4 = (n % 4) ^ 2 % 4 := by
    rw [Nat.pow_mod]
  have h4 : n % 4 < 4 := Nat.mod_lt _ (by norm_num)
  interval_cases hn : (n % 4) <;> simp [h]

/-- **Fermat's two–squares theorem.** A prime `p` is a sum of two squares if and only if
`p = 2` or `p ≡ 1 (mod 4)`. -/
theorem sum_two_squares (p : ℕ) (hp : p.Prime) :
    (∃ a b : ℕ, a ^ 2 + b ^ 2 = p) ↔ (p = 2 ∨ p % 4 = 1) := by
  constructor
  · rintro ⟨a, b, hab⟩
    have hmod : p % 4 ≠ 3 := by
      rcases sq_mod_four a with ha | ha <;> rcases sq_mod_four b with hb | hb <;>
        omega
    have hcase : p % 4 = 0 ∨ p % 4 = 1 ∨ p % 4 = 2 ∨ p % 4 = 3 := by omega
    rcases hcase with h | h | h | h
    · exfalso
      have h2 : 2 ∣ p := by omega
      have : p = 2 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2).symm
      omega
    · exact Or.inr h
    · left
      have h2 : 2 ∣ p := by omega
      exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2).symm
    · exact absurd h hmod
  · intro h
    haveI : Fact p.Prime := ⟨hp⟩
    have hmod : p % 4 ≠ 3 := by rcases h with h | h <;> omega
    exact Nat.Prime.sq_add_sq hmod

end Math

#print axioms Math.sum_two_squares

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

