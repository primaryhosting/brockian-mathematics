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
# Sierpinski Problem
Category: Brockian Conjecture
Target: Brockian.SierpinskiCovering.SierpinskiProblem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

set_option autoImplicit false

namespace Brockian
namespace SierpinskiCovering

/-- The covering table: for a residue `r` of the exponent modulo `36`, this list records a
small prime that divides `78557 * 2 ^ r + 1` (and also divides `2 ^ 36 - 1`, so that the
divisibility only depends on the exponent modulo `36`).

The primes used are `3, 5, 7, 13, 19, 37, 73`, which form the classical covering system
for the Sierpiński number `78557`. -/
def coverTable : List ℕ :=
  [3, 5, 3, 73, 3, 5, 3, 7, 3, 5, 3, 13, 3, 5, 3, 19, 3, 5, 3, 7,
   3, 5, 3, 13, 3, 5, 3, 37, 3, 5, 3, 7, 3, 5, 3, 13]

/-- The prime of the covering system attached to an exponent `n`, namely the entry of
`coverTable` at index `n % 36`. -/
def coverPrime (n : ℕ) : ℕ := coverTable.getD (n % 36) 3

/-- Every entry of the covering table is a prime at most `73` which divides `2 ^ 36 - 1`
and divides `78557 * 2 ^ r + 1` for its residue `r`. -/
lemma coverTable_spec :
    ∀ r ∈ Finset.range 36,
      Nat.Prime (coverTable.getD r 3) ∧
      coverTable.getD r 3 ≤ 73 ∧
      coverTable.getD r 3 ∣ 2 ^ 36 - 1 ∧
      coverTable.getD r 3 ∣ 78557 * 2 ^ r + 1 := by
  decide

lemma coverTable_spec' (n : ℕ) :
    Nat.Prime (coverPrime n) ∧ coverPrime n ≤ 73 ∧ coverPrime n ∣ 2 ^ 36 - 1 ∧
      coverPrime n ∣ 78557 * 2 ^ (n % 36) + 1 :=
  coverTable_spec (n % 36) (Finset.mem_range.mpr (Nat.mod_lt _ (by norm_num)))

lemma coverPrime_prime (n : ℕ) : Nat.Prime (coverPrime n) := (coverTable_spec' n).1

lemma coverPrime_dvd_pow_sub_one (n : ℕ) : coverPrime n ∣ 2 ^ 36 - 1 := (coverTable_spec' n).2.2.1

/-- If `p` divides `2 ^ 36 - 1`, then modulo `p` the power `2 ^ n` only depends on `n % 36`. -/
lemma two_pow_modEq_of_dvd {p n : ℕ} (hp : p ∣ 2 ^ 36 - 1) :
    (2 : ℕ) ^ n ≡ 2 ^ (n % 36) [MOD p] := by
  have h36 : (2 : ℕ) ^ 36 ≡ 1 [MOD p] :=
    ((Nat.modEq_iff_dvd' (by norm_num)).mpr hp).symm
  calc (2 : ℕ) ^ n = (2 ^ 36) ^ (n / 36) * 2 ^ (n % 36) := by
        rw [← pow_mul, ← pow_add, Nat.div_add_mod]
    _ ≡ 1 ^ (n / 36) * 2 ^ (n % 36) [MOD p] := Nat.ModEq.mul_right _ (h36.pow _)
    _ = 2 ^ (n % 36) := by ring

/-- The covering prime attached to `n` indeed divides `78557 * 2 ^ n + 1`. -/
theorem coverPrime_dvd (n : ℕ) : coverPrime n ∣ 78557 * 2 ^ n + 1 := by
  have hpow : (2 : ℕ) ^ n ≡ 2 ^ (n % 36) [MOD coverPrime n] :=
    two_pow_modEq_of_dvd (coverPrime_dvd_pow_sub_one n)
  have hN : 78557 * 2 ^ n + 1 ≡ 78557 * 2 ^ (n % 36) + 1 [MOD coverPrime n] :=
    (hpow.mul_left 78557).add_right 1
  have hzero : 78557 * 2 ^ (n % 36) + 1 ≡ 0 [MOD coverPrime n] :=
    Nat.modEq_zero_iff_dvd.mpr (coverTable_spec' n).2.2.2
  exact Nat.modEq_zero_iff_dvd.mp (hN.trans hzero)

lemma coverPrime_lt (n : ℕ) : coverPrime n < 78557 * 2 ^ n + 1 := by
  have h : coverPrime n ≤ 73 := (coverTable_spec' n).2.1
  have h2 : (1 : ℕ) ≤ 2 ^ n := Nat.one_le_two_pow
  nlinarith

/-- **The Sierpiński problem: `78557` is a Sierpiński number.**
For every natural number `n`, the number `78557 * 2 ^ n + 1` is composite (never prime).

The proof exhibits the classical covering system with the primes
`{3, 5, 7, 13, 19, 37, 73}`, each of which divides `2 ^ 36 - 1`, so that the residue of
`78557 * 2 ^ n + 1` modulo each of them depends only on `n % 36`. -/
theorem SierpinskiProblem (n : ℕ) : ¬ Nat.Prime (78557 * 2 ^ n + 1) := by
  intro hprime
  have hdvd := coverPrime_dvd n
  have hlt := coverPrime_lt n
  have hp := coverPrime_prime n
  rcases hprime.eq_one_or_self_of_dvd _ hdvd with h | h
  · exact hp.one_lt.ne' h
  · omega

/-- A quantitative restatement: every number of the form `78557 * 2 ^ n + 1` has a prime
factor which is strictly smaller than it (indeed one of `3, 5, 7, 13, 19, 37, 73`). -/
theorem exists_small_prime_factor (n : ℕ) :
    ∃ p, Nat.Prime p ∧ p ≤ 73 ∧ p ∣ 78557 * 2 ^ n + 1 ∧ p < 78557 * 2 ^ n + 1 :=
  ⟨coverPrime n, coverPrime_prime n, (coverTable_spec' n).2.1, coverPrime_dvd n, coverPrime_lt n⟩

end SierpinskiCovering
end Brockian

