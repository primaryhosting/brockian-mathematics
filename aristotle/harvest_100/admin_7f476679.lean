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
# Riesel Problem
Category: Brockian Conjecture
Target: Brockian.RieselCovering.RieselProblem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.RieselCovering

/-- The Riesel number under consideration: `509203`. -/
def k : ℕ := 509203

/-- The covering set assignment: for a residue `r` of the exponent modulo `24`,
`coverPrime r` is a prime dividing `k * 2 ^ n - 1` whenever `n ≡ r [MOD 24]`. -/
def coverPrime (r : ℕ) : ℕ :=
  [3, 5, 3, 241, 3, 5, 3, 13, 3, 5, 3, 7,
   3, 5, 3, 17, 3, 5, 3, 13, 3, 5, 3, 7].getD r 3

lemma coverPrime_mem (r : ℕ) : coverPrime r = 3 ∨ coverPrime r = 5 ∨ coverPrime r = 7 ∨
    coverPrime r = 13 ∨ coverPrime r = 17 ∨ coverPrime r = 241 := by
  rcases lt_or_ge r 24 with hr | hr
  · interval_cases r <;> simp [coverPrime]
  · left
    have hnone : ([3, 5, 3, 241, 3, 5, 3, 13, 3, 5, 3, 7,
        3, 5, 3, 17, 3, 5, 3, 13, 3, 5, 3, 7] : List ℕ)[r]? = none :=
      List.getElem?_eq_none (by simpa using hr)
    simp [coverPrime, List.getD_eq_getElem?_getD, hnone]

/-- Every member of the covering set is prime. -/
lemma coverPrime_prime (r : ℕ) : Nat.Prime (coverPrime r) := by
  rcases coverPrime_mem r with h | h | h | h | h | h <;> rw [h] <;> norm_num

/-- Every member of the covering set is at most `241`. -/
lemma coverPrime_le (r : ℕ) : coverPrime r ≤ 241 := by
  rcases coverPrime_mem r with h | h | h | h | h | h <;> rw [h] <;> norm_num

/-- `2` has multiplicative order dividing `24` modulo each covering prime. -/
lemma two_pow_24_mod (r : ℕ) : 2 ^ 24 % coverPrime r = 1 := by
  rcases coverPrime_mem r with h | h | h | h | h | h <;> rw [h] <;> rfl

/-- Periodicity of powers of two modulo a number `p` with `2 ^ 24 ≡ 1 [MOD p]`. -/
lemma two_pow_mod_period {p : ℕ} (hp : 2 ^ 24 % p = 1) (n : ℕ) :
    2 ^ n % p = 2 ^ (n % 24) % p := by
  conv_lhs => rw [← Nat.div_add_mod n 24, pow_add, pow_mul]
  rw [Nat.mul_mod, Nat.pow_mod, hp, one_pow, ← Nat.mul_mod, one_mul]

/-- The covering property at each residue: `k * 2 ^ r ≡ 1` modulo the assigned prime. -/
lemma cover_residue {r : ℕ} (hr : r < 24) : (k * 2 ^ r) % coverPrime r = 1 := by
  interval_cases r <;> rfl

/-- For every exponent `n`, the assigned covering prime divides `k * 2 ^ n - 1`. -/
lemma coverPrime_dvd (n : ℕ) : coverPrime (n % 24) ∣ k * 2 ^ n - 1 := by
  set p := coverPrime (n % 24) with hpdef
  have hmod : (k * 2 ^ n) % p = 1 := by
    rw [Nat.mul_mod, two_pow_mod_period (two_pow_24_mod (n % 24)) n, ← Nat.mul_mod]
    exact cover_residue (Nat.mod_lt _ (by norm_num))
  have hdm := Nat.div_add_mod (k * 2 ^ n) p
  exact ⟨(k * 2 ^ n) / p, by omega⟩

/-- **The Riesel problem, covering-set half.**
`509203` is a Riesel number: for every `n`, the number `509203 * 2 ^ n - 1` is composite
(not prime).  This is witnessed by the covering set `{3, 5, 7, 13, 17, 241}` of primes,
which divides the sequence periodically with period `24`. -/
theorem RieselProblem (n : ℕ) : ¬ Nat.Prime (509203 * 2 ^ n - 1) := by
  intro hprime
  have hdvd : coverPrime (n % 24) ∣ 509203 * 2 ^ n - 1 := coverPrime_dvd n
  have hple : coverPrime (n % 24) ≤ 241 := coverPrime_le (n % 24)
  have hp1 : 2 ≤ coverPrime (n % 24) := (coverPrime_prime (n % 24)).two_le
  have hbig : 509203 ≤ 509203 * 2 ^ n :=
    Nat.le_mul_of_pos_right _ (by positivity)
  have := hprime.eq_one_or_self_of_dvd _ hdvd
  omega

end Brockian.RieselCovering

