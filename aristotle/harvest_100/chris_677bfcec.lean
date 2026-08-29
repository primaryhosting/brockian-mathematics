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
# Woodall Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.CullenWoodall.WoodallPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Header kept verbatim, except that it is a plain block comment `/- -/` rather than a
-- module docstring `/-! -/`: Lean 4 does not allow any command, including a module
-- docstring, to precede the `import` section of a file.)

import Mathlib

namespace Brockian.CullenWoodall

/-- The `n`-th Woodall number `W n = n * 2 ^ n - 1` (natural subtraction; for `n ≥ 1`
this agrees with the usual integer definition). -/
def woodall (n : ℕ) : ℕ := n * 2 ^ n - 1

/-- A *Woodall prime* is a prime of the form `n * 2 ^ n - 1` with `n ≥ 1`. -/
def IsWoodallPrime (p : ℕ) : Prop := p.Prime ∧ ∃ n, 1 ≤ n ∧ p = woodall n

/-- The set of Woodall primes. -/
def woodallPrimes : Set ℕ := {p | IsWoodallPrime p}

section Basic

lemma one_le_mul_pow {n : ℕ} (hn : 1 ≤ n) : 1 ≤ n * 2 ^ n := by
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  calc 1 = 1 * 1 := by ring
  _ ≤ n * 2 ^ n := Nat.mul_le_mul hn h1

lemma succ_le_mul_pow {n : ℕ} (hn : 1 ≤ n) : n + 1 ≤ n * 2 ^ n := by
  have h2 : 2 ≤ 2 ^ n := by
    calc (2:ℕ) = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  calc n + 1 ≤ n + n := by omega
  _ = n * 2 := by ring
  _ ≤ n * 2 ^ n := Nat.mul_le_mul_left _ h2

/-- Woodall numbers grow at least as fast as the index. -/
lemma le_woodall {n : ℕ} (hn : 1 ≤ n) : n ≤ woodall n := by
  have := succ_le_mul_pow hn
  simp only [woodall]
  omega

/-- Strict monotonicity of `woodall` on positive indices. -/
lemma woodall_lt_woodall {m n : ℕ} (hm : 1 ≤ m) (h : m < n) : woodall m < woodall n := by
  have h1 : 1 ≤ m * 2 ^ m := one_le_mul_pow hm
  have h2 : m * 2 ^ m < n * 2 ^ n := by
    calc m * 2 ^ m < n * 2 ^ m := by gcongr
    _ ≤ n * 2 ^ n := by gcongr; norm_num
  simp only [woodall]
  omega

lemma woodall_le_woodall {m n : ℕ} (hm : 1 ≤ m) (h : m ≤ n) : woodall m ≤ woodall n := by
  rcases eq_or_lt_of_le h with rfl | h
  · exact le_rfl
  · exact (woodall_lt_woodall hm h).le

/-- A strictly larger Woodall value forces a strictly larger index. -/
lemma lt_of_woodall_lt {m n : ℕ} (hn : 1 ≤ n) (h : woodall m < woodall n) : m < n := by
  by_contra hcon
  exact absurd (woodall_le_woodall hn (Nat.le_of_not_lt hcon)) (not_le.mpr h)

end Basic

section Examples

lemma woodall_two : woodall 2 = 7 := by norm_num [woodall]
lemma woodall_three : woodall 3 = 23 := by norm_num [woodall]
lemma woodall_six : woodall 6 = 383 := by norm_num [woodall]

/-- `7 = 2 * 2 ^ 2 - 1` is a Woodall prime. -/
theorem isWoodallPrime_seven : IsWoodallPrime 7 :=
  ⟨by norm_num, 2, by norm_num, woodall_two.symm⟩

/-- `23 = 3 * 2 ^ 3 - 1` is a Woodall prime. -/
theorem isWoodallPrime_twentythree : IsWoodallPrime 23 :=
  ⟨by norm_num, 3, by norm_num, woodall_three.symm⟩

/-- `383 = 6 * 2 ^ 6 - 1` is a Woodall prime. -/
theorem isWoodallPrime_383 : IsWoodallPrime 383 :=
  ⟨by norm_num, 6, by norm_num, woodall_six.symm⟩

/-- Unconditionally, Woodall primes exist. -/
theorem woodallPrimes_nonempty : woodallPrimes.Nonempty :=
  ⟨7, isWoodallPrime_seven⟩

end Examples

section Divisors

/-- Every odd prime `p` divides some Woodall number `W n` with `n` arbitrarily large.
An unconditional partial result: no odd prime is excluded from the divisors of Woodall
numbers, so there is no congruence obstruction of that kind to large Woodall primes. -/
theorem exists_large_dvd_woodall (p : ℕ) (hp : p.Prime) (hodd : p ≠ 2) (N : ℕ) :
    ∃ n, N < n ∧ p ∣ woodall n := by
  haveI := Fact.mk hp
  have hp2 : 2 ≤ p := hp.two_le
  have hpodd : p % 2 = 1 := (hp.eq_two_or_odd).resolve_left hodd
  have hp3 : 3 ≤ p := by omega
  set q : ℕ := (p + 1) / 2 with hq
  have h2q : 2 * q = p + 1 := by omega
  set t : ℕ := N + 1 with ht
  set k : ℕ := q + t * p with hk
  set n : ℕ := 1 + k * (p - 1) with hn
  have hn1 : 1 ≤ n := by omega
  have hNn : N < n := by
    have h1 : t ≤ k := by nlinarith [Nat.zero_le q]
    have h2 : k ≤ k * (p - 1) := Nat.le_mul_of_pos_right k (by omega)
    omega
  refine ⟨n, hNn, ?_⟩
  have hpne : ((p : ℕ) : ZMod p) = 0 := ZMod.natCast_self p
  have h2ne : (2 : ZMod p) ≠ 0 := by
    have hnd : ¬ (p ∣ 2) := fun h => hodd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
    intro hh
    exact hnd ((ZMod.natCast_eq_zero_iff 2 p).mp (by exact_mod_cast hh))
  have hpm1 : ((p - 1 : ℕ) : ZMod p) = -1 := by
    rw [Nat.cast_sub hp.one_le, hpne]; simp
  have h2k : (2 : ZMod p) * (k : ZMod p) = 1 := by
    have h1 : 2 * k = (p + 1) + 2 * t * p := by rw [hk]; ring_nf; omega
    have h2 : ((2 * k : ℕ) : ZMod p) = ((p + 1 + 2 * t * p : ℕ) : ZMod p) := by rw [h1]
    push_cast [hpne] at h2
    rw [h2]; ring
  have hncast : ((n : ℕ) : ZMod p) = 1 - (k : ZMod p) := by
    rw [hn]; push_cast [hpm1]; ring
  have hpow : (2 : ZMod p) ^ n = 2 := by
    have hfermat : (2 : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one h2ne
    calc (2 : ZMod p) ^ n = 2 ^ (1 + k * (p - 1)) := by rw [hn]
    _ = 2 * ((2 : ZMod p) ^ (p - 1)) ^ k := by rw [pow_add, ← pow_mul, mul_comm k (p - 1)]; ring
    _ = 2 := by rw [hfermat]; simp
  have key : ((n * 2 ^ n : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
    push_cast
    rw [hncast, hpow]
    linear_combination -h2k
  have hmod : (1 : ℕ) ≡ n * 2 ^ n [MOD p] := ((ZMod.natCast_eq_natCast_iff _ _ _).mp key).symm
  have hge : 1 ≤ n * 2 ^ n := Nat.mul_pos (by omega) (Nat.two_pow_pos n)
  exact (Nat.modEq_iff_dvd' hge).mp hmod

end Divisors

/-!
### The main reduction

Whether there are infinitely many Woodall primes is an open problem, so the statement below
is a *conditional reduction*: the infinitude of the set of Woodall primes is proved
equivalent to the statement that the index set `{n | (n * 2 ^ n - 1).Prime}` is unbounded.
-/

/-- **Woodall prime infinitude (conditional reduction).**
The set of Woodall primes is infinite if and only if there are arbitrarily large indices `n`
for which the Woodall number `n * 2 ^ n - 1` is prime. -/
theorem WoodallPrimeInfinitude :
    woodallPrimes.Infinite ↔ ∀ N : ℕ, ∃ n, N < n ∧ Nat.Prime (woodall n) := by
  constructor
  · intro hinf N
    obtain ⟨p, hp, hlt⟩ := hinf.exists_gt (woodall (max N 1))
    obtain ⟨hprime, n, hn1, rfl⟩ := hp
    have hmax : max N 1 < n := lt_of_woodall_lt hn1 hlt
    exact ⟨n, lt_of_le_of_lt (le_max_left N 1) hmax, hprime⟩
  · intro H
    rw [Set.infinite_iff_exists_gt]
    intro a
    obtain ⟨n, hn, hprime⟩ := H (max a 1)
    have h1 : 1 ≤ n := le_trans (le_max_right a 1) hn.le
    have ha : a < n := lt_of_le_of_lt (le_max_left a 1) hn
    exact ⟨woodall n, ⟨hprime, n, h1, rfl⟩, lt_of_lt_of_le ha (le_woodall h1)⟩

/-- The forward implication of the reduction, stated separately: unbounded prime indices
give infinitely many Woodall primes. -/
theorem woodallPrimes_infinite_of_unbounded_indices
    (H : ∀ N : ℕ, ∃ n, N < n ∧ Nat.Prime (woodall n)) : woodallPrimes.Infinite :=
  WoodallPrimeInfinitude.mpr H

end Brockian.CullenWoodall

