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

namespace Math

/-- A perfect square is congruent to `0` or `1` modulo `4`. -/
theorem sq_mod_four_eq_zero_or_one (a : ℕ) : a ^ 2 % 4 = 0 ∨ a ^ 2 % 4 = 1 := by
  rcases Nat.even_or_odd a with ⟨k, hk⟩ | ⟨k, hk⟩
  · left
    subst hk
    have h : (k + k) ^ 2 = 4 * (k * k) := by ring
    rw [h, Nat.mul_mod_right]
  · right
    subst hk
    have h : (2 * k + 1) ^ 2 = 4 * (k * k + k) + 1 := by ring
    rw [h, Nat.mul_add_mod]

/-- A sum of two squares is never congruent to `3` modulo `4`. -/
theorem mod_four_ne_three_of_sq_add_sq {n a b : ℕ} (h : n = a ^ 2 + b ^ 2) : n % 4 ≠ 3 := by
  have ha := sq_mod_four_eq_zero_or_one a
  have hb := sq_mod_four_eq_zero_or_one b
  have hmod := Nat.add_mod (a ^ 2) (b ^ 2) 4
  omega

/-- **Fermat's two-square theorem**: a prime `p` is a sum of two squares if and only if
`p = 2` or `p ≡ 1 [MOD 4]`.  (The hard direction uses `Nat.Prime.sq_add_sq` from Mathlib.) -/
theorem sum_two_squares {p : ℕ} (hp : Nat.Prime p) :
    (∃ a b : ℕ, p = a ^ 2 + b ^ 2) ↔ (p = 2 ∨ p % 4 = 1) := by
  constructor
  · rintro ⟨a, b, hab⟩
    have h3 : p % 4 ≠ 3 := mod_four_ne_three_of_sq_add_sq hab
    rcases hp.eq_two_or_odd with h2 | h2
    · exact Or.inl h2
    · exact Or.inr (by omega)
  · intro h
    haveI : Fact (Nat.Prime p) := ⟨hp⟩
    have h3 : p % 4 ≠ 3 := by rcases h with h | h <;> omega
    obtain ⟨a, b, hab⟩ := Nat.Prime.sq_add_sq h3
    exact ⟨a, b, hab.symm⟩

end Math

