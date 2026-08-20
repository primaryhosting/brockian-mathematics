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

/-!
# Riesel Problem
Category: Brockian Conjecture
Target: Brockian.RieselCovering.RieselProblem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian
namespace RieselCovering

/-- A *Riesel number* is an odd natural number `k` such that `k * 2 ^ n - 1` is
composite for every `n ≥ 1`. -/
def IsRiesel (k : ℕ) : Prop :=
  Odd k ∧ ∀ n : ℕ, 1 ≤ n → ¬ Nat.Prime (k * 2 ^ n - 1)

/-- The covering set assigns to each residue `r` of `n` modulo `24` a prime dividing
`509203 * 2 ^ n - 1`.  The primes used are `3, 5, 7, 13, 17, 241`. -/
def coverPrime (r : ℕ) : ℕ :=
  [3, 5, 3, 241, 3, 5, 3, 13, 3, 5, 3, 7,
   3, 5, 3, 17, 3, 5, 3, 13, 3, 5, 3, 7].getD r 3

lemma coverPrime_le (r : ℕ) (hr : r < 24) : coverPrime r ≤ 241 := by
  interval_cases r <;> decide

lemma coverPrime_pow24 (r : ℕ) (hr : r < 24) :
    2 ^ 24 % coverPrime r = 1 % coverPrime r := by
  interval_cases r <;> decide

lemma coverPrime_dvd_base (r : ℕ) (hr : r < 24) :
    509203 * 2 ^ r % coverPrime r = 1 % coverPrime r := by
  interval_cases r <;> decide

/-- The key covering property: for every `n`, one of the six primes divides
`509203 * 2 ^ n - 1`. -/
theorem coverPrime_dvd (n : ℕ) : coverPrime (n % 24) ∣ 509203 * 2 ^ n - 1 := by
  have hr : n % 24 < 24 := Nat.mod_lt _ (by norm_num)
  set r := n % 24
  set p := coverPrime r
  have h24 : (2 : ℕ) ^ 24 ≡ 1 [MOD p] := coverPrime_pow24 r hr
  have hq : ((2 : ℕ) ^ 24) ^ (n / 24) ≡ 1 [MOD p] := by
    simpa using h24.pow (n / 24)
  have hn : 24 * (n / 24) + r = n := Nat.div_add_mod n 24
  have hsplit : (2 : ℕ) ^ n = ((2 : ℕ) ^ 24) ^ (n / 24) * 2 ^ r := by
    rw [← pow_mul, ← pow_add, hn]
  have hbase : 509203 * 2 ^ r ≡ 1 [MOD p] := coverPrime_dvd_base r hr
  have hmain : 509203 * 2 ^ n ≡ 1 [MOD p] := by
    calc 509203 * 2 ^ n = ((2 : ℕ) ^ 24) ^ (n / 24) * (509203 * 2 ^ r) := by
          rw [hsplit]; ring
      _ ≡ 1 * 1 [MOD p] := hq.mul hbase
      _ = 1 := by ring
  have h1 : 1 ≤ 509203 * 2 ^ n := Nat.one_le_iff_ne_zero.2 (by positivity)
  exact (Nat.modEq_iff_dvd' h1).1 hmain.symm

lemma coverPrime_prime (r : ℕ) (hr : r < 24) : Nat.Prime (coverPrime r) := by
  interval_cases r <;> norm_num [coverPrime]

/-- `509203` is a Riesel number. -/
theorem isRiesel_509203 : IsRiesel 509203 := by
  refine ⟨⟨254601, by norm_num⟩, ?_⟩
  intro n hn hprime
  have hr : n % 24 < 24 := Nat.mod_lt _ (by norm_num)
  have hdvd := coverPrime_dvd n
  have hple : coverPrime (n % 24) ≤ 241 := coverPrime_le _ hr
  have hpp : Nat.Prime (coverPrime (n % 24)) := coverPrime_prime _ hr
  have hbig : 1018405 ≤ 509203 * 2 ^ n - 1 := by
    have h2 : (2 : ℕ) ^ 1 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have : 509203 * 2 ≤ 509203 * 2 ^ n := Nat.mul_le_mul_left _ (by simpa using h2)
    omega
  rcases (Nat.Prime.eq_one_or_self_of_dvd hprime _ hdvd) with h | h
  · exact hpp.one_lt.ne' h
  · omega

/-- **The Riesel problem.**  The least Riesel number is at most `509203`, witnessed by the
covering set `{3, 5, 7, 13, 17, 241}` of the residues modulo `24`:  `509203` itself is a
Riesel number, i.e. `509203 * 2 ^ n - 1` is composite for every `n ≥ 1`.
(That `509203` is exactly the least such number is an open problem.) -/
theorem RieselProblem :
    IsRiesel 509203 ∧ sInf {k : ℕ | IsRiesel k} ≤ 509203 :=
  ⟨isRiesel_509203, Nat.sInf_le isRiesel_509203⟩

/-- Conditional reduction of the Riesel problem: since `509203` is a Riesel number, it is the
least one as soon as no smaller natural number is Riesel. -/
theorem isLeast_riesel_of_no_smaller (h : ∀ k < 509203, ¬ IsRiesel k) :
    IsLeast {k : ℕ | IsRiesel k} 509203 := by
  refine ⟨isRiesel_509203, ?_⟩
  intro k hk
  by_contra hlt
  exact h k (by omega) hk

end RieselCovering
end Brockian

