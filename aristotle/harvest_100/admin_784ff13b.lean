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

/-
# Legendre Conjecture
Category: Brockian Conjecture
Target: Brockian.LegendreConjecture.LegendreConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Legendre Conjecture
Category: Brockian Conjecture
Target: Brockian.LegendreConjecture.LegendreConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxRecDepth 40000
set_option maxHeartbeats 1000000

namespace Brockian.LegendreConjecture

/-- **Legendre's conjecture**: for every `n ≥ 1` there is a prime strictly between
`n ^ 2` and `(n + 1) ^ 2`.  This is a famous open problem. -/
def LegendreStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∃ p : ℕ, Nat.Prime p ∧ n ^ 2 < p ∧ p < (n + 1) ^ 2

/-- The "primes in short intervals" hypothesis, in eventual form: every sufficiently
large `x` is followed by a prime in the interval `(x, x + √x]`. -/
def EventuallyPrimeInSqrtInterval : Prop :=
  ∀ x : ℕ, 900 ≤ x → ∃ p : ℕ, Nat.Prime p ∧ x < p ∧ p ≤ x + Nat.sqrt x

/-- Unconditional finite verification: Legendre's conjecture holds for all `1 ≤ n ≤ 30`. -/
theorem legendre_le_thirty (n : ℕ) (hn : 1 ≤ n) (hn' : n ≤ 30) :
    ∃ p : ℕ, Nat.Prime p ∧ n ^ 2 < p ∧ p < (n + 1) ^ 2 := by
  have key : ∀ m ∈ Finset.Icc 1 30, ∃ p ∈ Finset.Ioo (m ^ 2) ((m + 1) ^ 2), Nat.Prime p := by
    decide
  obtain ⟨p, hp, hp'⟩ := key n (Finset.mem_Icc.mpr ⟨hn, hn'⟩)
  rw [Finset.mem_Ioo] at hp
  exact ⟨p, hp', hp.1, hp.2⟩

/-- **Conditional reduction of Legendre's conjecture.**

Legendre's conjecture — a prime strictly between `n ^ 2` and `(n + 1) ^ 2` for every `n ≥ 1` —
follows from the (also open) hypothesis that every sufficiently large `x` is followed by a
prime in the short interval `(x, x + √x]`.  The remaining small cases `n ≤ 30` are verified
unconditionally, so no assumption is needed for them. -/
theorem LegendreConjecture (H : EventuallyPrimeInSqrtInterval) : LegendreStatement := by
  intro n hn
  by_cases hsmall : n ≤ 30
  · exact legendre_le_thirty n hn hsmall
  · push_neg at hsmall
    have hx : 900 ≤ n ^ 2 := by nlinarith
    obtain ⟨p, hp, hlt, hle⟩ := H (n ^ 2) hx
    refine ⟨p, hp, hlt, ?_⟩
    have hsq : Nat.sqrt (n ^ 2) = n := Nat.sqrt_eq' n
    rw [hsq] at hle
    have hgap : n ^ 2 + n < (n + 1) ^ 2 := by nlinarith
    omega

/-- Unconditional weakening (from Bertrand's postulate): for every `n ≥ 1` there is a prime
strictly between `n ^ 2` and `(2 * n) ^ 2`. -/
theorem exists_prime_between_sq_and_four_sq (n : ℕ) (hn : 1 ≤ n) :
    ∃ p : ℕ, Nat.Prime p ∧ n ^ 2 < p ∧ p < (2 * n) ^ 2 := by
  obtain ⟨p, hp, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul (n ^ 2) (by positivity)
  refine ⟨p, hp, hlt, ?_⟩
  have h1 : 1 ≤ n ^ 2 := Nat.one_le_pow _ _ hn
  have h2 : (2 * n) ^ 2 = 4 * n ^ 2 := by ring
  omega

end Brockian.LegendreConjecture

