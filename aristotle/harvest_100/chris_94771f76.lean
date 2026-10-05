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
# Landau Fourth Conjecture
Category: Brockian Conjecture
Target: Brockian.LandauNSquaredPlusOne.LandauFourthConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Landau Fourth Conjecture
Category: Brockian Conjecture
Target: Brockian.LandauNSquaredPlusOne.LandauFourthConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.LandauNSquaredPlusOne

/-- The set of natural numbers `n` such that `n ^ 2 + 1` is prime.
Landau's fourth problem asserts that this set is infinite; it is open. -/
def LandauSet : Set ℕ := {n | Nat.Prime (n ^ 2 + 1)}

/-- The *sieve condition*: for every bound `N` there is some `n > N` such that no prime
`p ≤ n` divides `n ^ 2 + 1`.  This is an elementary reformulation of Landau's fourth
problem (see `landau_iff_noSmallPrimeFactor`). -/
def NoSmallPrimeFactorCondition : Prop :=
  ∀ N : ℕ, ∃ n : ℕ, N < n ∧ ∀ p : ℕ, p.Prime → p ≤ n → ¬ p ∣ n ^ 2 + 1

/-- Trial-division criterion: if `n ≥ 1` and no prime `p ≤ n` divides `n ^ 2 + 1`, then
`n ^ 2 + 1` is prime. -/
theorem prime_of_no_small_prime_factor {n : ℕ} (hn : 1 ≤ n)
    (h : ∀ p : ℕ, p.Prime → p ≤ n → ¬ p ∣ n ^ 2 + 1) : Nat.Prime (n ^ 2 + 1) := by
  by_contra hc
  have hpos : 0 < n ^ 2 + 1 := Nat.succ_pos _
  have hne1 : n ^ 2 + 1 ≠ 1 := by
    have : 1 ≤ n ^ 2 := Nat.one_le_pow _ _ hn
    omega
  have hprime : Nat.Prime (n ^ 2 + 1).minFac := Nat.minFac_prime hne1
  have hsq : (n ^ 2 + 1).minFac ^ 2 ≤ n ^ 2 + 1 := Nat.minFac_sq_le_self hpos hc
  have hle : (n ^ 2 + 1).minFac ≤ n := by
    by_contra hgt
    push_neg at hgt
    have h2 : (n + 1) ^ 2 ≤ (n ^ 2 + 1).minFac ^ 2 := Nat.pow_le_pow_left hgt 2
    nlinarith [hsq, h2]
  exact h _ hprime hle (Nat.minFac_dvd _)

/-- Conversely, if `n ^ 2 + 1` is prime then no prime `p ≤ n` divides it. -/
theorem no_small_prime_factor_of_prime {n : ℕ} (hp : Nat.Prime (n ^ 2 + 1)) :
    ∀ p : ℕ, p.Prime → p ≤ n → ¬ p ∣ n ^ 2 + 1 := by
  intro p hpp hpn hdvd
  have heq : p = n ^ 2 + 1 := (Nat.prime_dvd_prime_iff_eq hpp hp).mp hdvd
  have : n ^ 2 + 1 ≤ n := heq ▸ hpn
  nlinarith [Nat.zero_le n, sq_nonneg n]

/-- **Equivalent reformulation of Landau's fourth problem.**  There are infinitely many
primes of the form `n ^ 2 + 1` if and only if for every bound there is a larger `n`
such that `n ^ 2 + 1` is divisible by no prime `p ≤ n`. -/
theorem landau_iff_noSmallPrimeFactor :
    LandauSet.Infinite ↔ NoSmallPrimeFactorCondition := by
  constructor
  · intro hinf N
    obtain ⟨n, hn, hgt⟩ := Set.infinite_iff_exists_gt.mp hinf N
    exact ⟨n, hgt, no_small_prime_factor_of_prime hn⟩
  · intro h
    apply Set.infinite_of_forall_exists_gt
    intro N
    obtain ⟨n, hgt, hn⟩ := h (max N 1)
    refine ⟨n, prime_of_no_small_prime_factor ?_ hn, lt_of_le_of_lt (le_max_left N 1) hgt⟩
    exact le_of_lt (lt_of_le_of_lt (le_max_right N 1) hgt)

/-- **Landau's fourth conjecture, conditional on the elementary sieve condition
`NoSmallPrimeFactorCondition`.**  Assuming that arbitrarily large `n` have the property
that `n ^ 2 + 1` has no prime factor `p ≤ n`, there are infinitely many primes of the
form `n ^ 2 + 1`.

Landau's fourth problem is open, so the result is stated in this conditional form;
`landau_iff_noSmallPrimeFactor` shows that the hypothesis is in fact *equivalent* to the
conjecture, i.e. this is a faithful reduction and not a weakening. -/
theorem LandauFourthConjecture (h : NoSmallPrimeFactorCondition) :
    {n : ℕ | Nat.Prime (n ^ 2 + 1)}.Infinite :=
  landau_iff_noSmallPrimeFactor.mpr h

/-- Contrapositive form: Landau's fourth problem fails exactly when, beyond some bound,
every `n ^ 2 + 1` is caught by trial division with a prime `p ≤ n`. -/
theorem not_landau_iff :
    ¬ LandauSet.Infinite ↔
      ∃ N : ℕ, ∀ n : ℕ, N < n → ∃ p : ℕ, p.Prime ∧ p ≤ n ∧ p ∣ n ^ 2 + 1 := by
  rw [landau_iff_noSmallPrimeFactor, NoSmallPrimeFactorCondition]
  push_neg
  constructor
  · rintro ⟨N, hN⟩
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨p, hp, hpn, hdvd⟩ := hN n hn
    exact ⟨p, hp, hpn, hdvd⟩
  · rintro ⟨N, hN⟩
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨p, hp, hpn, hdvd⟩ := hN n hn
    exact ⟨p, hp, hpn, hdvd⟩

/-- Every prime `p` with `p % 4 ≠ 3` divides some value of the polynomial `X ^ 2 + 1`. -/
theorem exists_dvd_sq_add_one_of_prime {p : ℕ} (hp : p.Prime) (h4 : p % 4 ≠ 3) :
    ∃ n : ℕ, p ∣ n ^ 2 + 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨a, ha⟩ := (ZMod.exists_sq_eq_neg_one_iff (p := p)).mpr h4
  refine ⟨a.val, ?_⟩
  have hz : ((a.val ^ 2 + 1 : ℕ) : ZMod p) = 0 := by
    push_cast
    rw [ZMod.natCast_val, ZMod.cast_id, sq, ← ha]
    ring
  exact (ZMod.natCast_eq_zero_iff (a.val ^ 2 + 1) p).mp hz

/-- **Unconditional partial result.**  Infinitely many primes divide some value of
`n ^ 2 + 1`.  (The open conjecture asks for infinitely many primes that are *equal* to
some `n ^ 2 + 1`.) -/
theorem infinite_primes_dvd_sq_add_one :
    {p : ℕ | p.Prime ∧ ∃ n : ℕ, p ∣ n ^ 2 + 1}.Infinite := by
  have hsub : {p : ℕ | p.Prime ∧ p ≡ 1 [MOD 4]} ⊆ {p : ℕ | p.Prime ∧ ∃ n : ℕ, p ∣ n ^ 2 + 1} := by
    rintro p ⟨hp, hmod⟩
    refine ⟨hp, exists_dvd_sq_add_one_of_prime hp ?_⟩
    have h : p % 4 = 1 % 4 := hmod
    omega
  exact (Nat.infinite_setOf_prime_modEq_one (k := 4) (by norm_num)).mono hsub

/-- Every odd prime dividing a value `n ^ 2 + 1` is congruent to `1` modulo `4`. -/
theorem prime_mod_four_eq_one_of_dvd_sq_add_one {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hdvd : p ∣ n ^ 2 + 1) : p % 4 = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hsq : IsSquare (-1 : ZMod p) := by
    refine ⟨(n : ZMod p), ?_⟩
    have hz : ((n ^ 2 + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
    push_cast at hz
    linear_combination -hz
  have h3 : p % 4 ≠ 3 := (ZMod.exists_sq_eq_neg_one_iff (p := p)).mp hsq
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
  omega

/-- If `n ^ 2 + 1` is prime and `n > 1`, then `n` is even. -/
theorem even_of_prime_sq_add_one {n : ℕ} (hn : 1 < n) (hp : Nat.Prime (n ^ 2 + 1)) : Even n := by
  rcases Nat.even_or_odd n with h | h
  · exact h
  · exfalso
    obtain ⟨k, hk⟩ := h
    have h2 : 2 ∣ n ^ 2 + 1 := ⟨2 * k ^ 2 + 2 * k + 1, by subst hk; ring⟩
    have hcases := hp.eq_one_or_self_of_dvd 2 h2
    have hbig : 4 < n ^ 2 + 1 := by nlinarith
    omega

/-- A sharper sieve condition: it suffices to rule out prime divisors `p ≤ n` that are
congruent to `1` modulo `4`, for even `n`. -/
def NoSmallModOnePrimeFactorCondition : Prop :=
  ∀ N : ℕ, ∃ n : ℕ, N < n ∧ Even n ∧ ∀ p : ℕ, p.Prime → p % 4 = 1 → p ≤ n → ¬ p ∣ n ^ 2 + 1

/-- **Sharper equivalent reformulation of Landau's fourth problem**: there are infinitely many
primes of the form `n ^ 2 + 1` iff arbitrarily large even `n` avoid all prime divisors
`p ≤ n` with `p ≡ 1 [MOD 4]`. -/
theorem landau_iff_noSmallModOnePrimeFactor :
    LandauSet.Infinite ↔ NoSmallModOnePrimeFactorCondition := by
  constructor
  · intro hinf N
    obtain ⟨n, hn, hgt⟩ := Set.infinite_iff_exists_gt.mp hinf (max N 1)
    refine ⟨n, lt_of_le_of_lt (le_max_left N 1) hgt,
      even_of_prime_sq_add_one (lt_of_le_of_lt (le_max_right N 1) hgt) hn, ?_⟩
    intro p hpp _ hpn
    exact no_small_prime_factor_of_prime hn p hpp hpn
  · intro h
    apply Set.infinite_of_forall_exists_gt
    intro N
    obtain ⟨n, hgt, heven, hn⟩ := h (max N 1)
    have hn1 : 1 ≤ n := le_of_lt (lt_of_le_of_lt (le_max_right N 1) hgt)
    refine ⟨n, prime_of_no_small_prime_factor hn1 ?_, lt_of_le_of_lt (le_max_left N 1) hgt⟩
    intro p hpp hpn hdvd
    have hp2 : p ≠ 2 := by
      rintro rfl
      obtain ⟨k, hk⟩ := heven
      have h2 : (2 : ℕ) ∣ n ^ 2 := ⟨2 * k ^ 2, by subst hk; ring⟩
      omega
    exact hn p hpp (prime_mod_four_eq_one_of_dvd_sq_add_one hpp hp2 hdvd) hpn hdvd

/-- Small members of `LandauSet`: for `n = 1, 2, 4, 6, 10, 14, 16, 20` the numbers
`2, 5, 17, 37, 101, 197, 257, 401` are prime. -/
theorem mem_landauSet_examples : ({1, 2, 4, 6, 10, 14, 16, 20} : Set ℕ) ⊆ LandauSet := by
  intro n hn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    · simp only [LandauSet, Set.mem_setOf_eq]
      norm_num

end Brockian.LandauNSquaredPlusOne

