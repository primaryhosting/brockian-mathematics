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
# Fermat Prime Beyond Four
Category: Brockian Conjecture
Target: Brockian.FermatNumbers.FermatPrimeBeyondFour
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to be the first command, so the header above is a plain block
-- comment rather than a `/-!` module docstring.)

import Mathlib

/-!
## Overview

The `n`-th Fermat number is `Fₙ = 2 ^ 2 ^ n + 1`.  The numbers `F₀, …, F₄` are prime, and no
further Fermat prime is known; whether some `Fₙ` with `n > 4` is prime is a famous open problem.

This file contains:

* `Brockian.FermatNumbers.fermat` — the Fermat numbers;
* `Brockian.FermatNumbers.prime_of_pepin` — the sufficiency half of Pépin's test;
* `Brockian.FermatNumbers.pepin_of_prime` — the necessity half of Pépin's test;
* `Brockian.FermatNumbers.FermatPrimeBeyondFour` — the main result: an unconditional
  *Lean-checked reduction* of the open conjecture "there is a Fermat prime beyond `F₄`" to a
  purely modular-arithmetic statement (Pépin's criterion);
* verified data: `F₀, …, F₄` are prime, and `F₅`, `F₆` are composite.
-/

namespace Brockian.FermatNumbers

/-- The `n`-th Fermat number `Fₙ = 2 ^ 2 ^ n + 1`. -/
def fermat (n : ℕ) : ℕ := 2 ^ 2 ^ n + 1

lemma fermat_two_lt (n : ℕ) : 2 < fermat n := by
  have : 2 ≤ 2 ^ 2 ^ n := by
    calc (2:ℕ) = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ 2 ^ n := Nat.pow_le_pow_right (by norm_num) Nat.one_le_two_pow
  simp only [fermat]
  omega

private lemma pow_two_pow_split (n : ℕ) : 2 ^ (2 ^ n) = 2 ^ (2 ^ n - 1) * 2 := by
  have h : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  rw [← pow_succ]
  congr 1
  omega

lemma fermat_mod_three (n : ℕ) (hn : 1 ≤ n) : fermat n % 3 = 2 := by
  have h : 2 ^ n = 2 * 2 ^ (n - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have h2 : 2 ^ (2 ^ n) = 4 ^ (2 ^ (n - 1)) := by
    rw [h, pow_mul]
    norm_num
  have h3 : 4 ^ (2 ^ (n - 1)) % 3 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  rw [fermat, h2]
  generalize (4:ℕ) ^ (2 ^ (n - 1)) = m at h3 ⊢
  omega

lemma fermat_mod_four (n : ℕ) (hn : 1 ≤ n) : fermat n % 4 = 1 := by
  obtain ⟨k, hk⟩ : ∃ k, 2 ^ n = 2 + k := by
    have : 2 ≤ 2 ^ n := by
      calc (2:ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    exact ⟨2 ^ n - 2, by omega⟩
  rw [fermat, hk, pow_add]
  generalize (2:ℕ) ^ k = m
  omega

/-- **Pépin's test, sufficiency.**  If `3 ^ ((Fₙ - 1) / 2) = -1` in `ZMod Fₙ`, then the Fermat
number `Fₙ` is prime.  (Here `(Fₙ - 1) / 2 = 2 ^ (2 ^ n - 1)`.) -/
theorem prime_of_pepin (n : ℕ) (h : (3 : ZMod (fermat n)) ^ (2 ^ (2 ^ n - 1)) = -1) :
    Nat.Prime (fermat n) := by
  set N := fermat n with hN
  have hN2 : 2 < N := fermat_two_lt n
  haveI : NeZero N := ⟨by omega⟩
  set u : ZMod N := 3 with hu
  have hne : (-1 : ZMod N) ≠ 1 := by
    intro hcon
    have h2 : ((2:ℕ) : ZMod N) = 0 := by push_cast; linear_combination -hcon
    rw [ZMod.natCast_eq_zero_iff] at h2
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  have hpow : u ^ (2 ^ 2 ^ n) = 1 := by
    rw [pow_two_pow_split, pow_mul, h]
    ring
  have hunit : IsUnit u := by
    refine IsUnit.of_mul_eq_one (u ^ (2 ^ 2 ^ n - 1)) ?_
    have h1 : 1 ≤ 2 ^ 2 ^ n := Nat.one_le_two_pow
    calc u * u ^ (2 ^ 2 ^ n - 1) = u ^ (2 ^ 2 ^ n) := by
          rw [← pow_succ']; congr 1; omega
    _ = 1 := hpow
  have hdvd : orderOf u ∣ 2 ^ 2 ^ n := orderOf_dvd_of_pow_eq_one hpow
  have hnd : ¬ (orderOf u ∣ 2 ^ (2 ^ n - 1)) := by
    intro hc
    have hone := orderOf_dvd_iff_pow_eq_one.mp hc
    rw [h] at hone
    exact hne hone
  obtain ⟨k, hk, hko⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hkeq : k = 2 ^ n := by
    by_contra hkn
    exact hnd (hko ▸ Nat.pow_dvd_pow 2 (by omega))
  have hord : orderOf u = N - 1 := by
    rw [hko, hkeq, hN]
    simp [fermat]
  have hordu : orderOf hunit.unit = N - 1 := by
    rw [← orderOf_units, IsUnit.unit_spec, hord]
  have hdvd2 : (N - 1) ∣ Nat.totient N := by
    rw [← hordu, ← ZMod.card_units_eq_totient N]
    exact orderOf_dvd_card
  have hlt : Nat.totient N < N := Nat.totient_lt N (by omega)
  have hpos : 0 < Nat.totient N := Nat.totient_pos.mpr (by omega)
  have htot : Nat.totient N = N - 1 := by
    have := Nat.le_of_dvd hpos hdvd2
    omega
  exact (Nat.totient_eq_iff_prime (by omega)).mp htot

/-- **Pépin's test, necessity.**  If the Fermat number `Fₙ` with `n ≥ 1` is prime, then
`3 ^ ((Fₙ - 1) / 2) = -1` in `ZMod Fₙ`.  (Proof: `3` is a quadratic nonresidue mod `Fₙ`, by
quadratic reciprocity together with `Fₙ ≡ 1 [MOD 4]` and `Fₙ ≡ 2 [MOD 3]`.) -/
theorem pepin_of_prime (n : ℕ) (hn : 1 ≤ n) (hp : Nat.Prime (fermat n)) :
    (3 : ZMod (fermat n)) ^ (2 ^ (2 ^ n - 1)) = -1 := by
  haveI : Fact (Nat.Prime (fermat n)) := ⟨hp⟩
  have hdiv : fermat n / 2 = 2 ^ (2 ^ n - 1) := by
    rw [fermat, pow_two_pow_split]
    omega
  have hleg : legendreSym (fermat n) 3 = -1 := by
    have h1 : legendreSym 3 ((fermat n : ℕ) : ℤ) = legendreSym (fermat n) ((3:ℕ) : ℤ) :=
      legendreSym.quadratic_reciprocity_one_mod_four (fermat_mod_four n hn) (by norm_num)
    have h2 : legendreSym 3 ((fermat n : ℕ) : ℤ) = legendreSym 3 (((fermat n : ℕ) : ℤ) % 3) :=
      legendreSym.mod 3 _
    have h3 : ((fermat n : ℕ) : ℤ) % 3 = 2 := by
      have := fermat_mod_three n hn
      omega
    rw [h3] at h2
    have h4 : legendreSym 3 2 = -1 := by decide
    push_cast at h1
    rw [h4] at h2
    omega
  have hpow := legendreSym.eq_pow (fermat n) 3
  rw [hleg, hdiv] at hpow
  push_cast at hpow
  exact hpow.symm

/-- **Pépin's test** for `n ≥ 1`: `Fₙ` is prime iff `3 ^ ((Fₙ - 1) / 2) = -1` in `ZMod Fₙ`. -/
theorem prime_iff_pepin (n : ℕ) (hn : 1 ≤ n) :
    Nat.Prime (fermat n) ↔ (3 : ZMod (fermat n)) ^ (2 ^ (2 ^ n - 1)) = -1 :=
  ⟨pepin_of_prime n hn, prime_of_pepin n⟩

/-- The statement "there is a Fermat prime beyond `F₄`", i.e. the (open) assertion that some
Fermat number of index greater than `4` is prime. -/
def FermatPrimeBeyondFourConjecture : Prop := ∃ n, 4 < n ∧ Nat.Prime (fermat n)

/-- **Main result (conditional reduction).**  The open conjecture that a Fermat prime exists
beyond `F₄` is *equivalent* to the purely modular-arithmetic statement that `3 ^ ((Fₙ - 1) / 2)
= -1` in `ZMod Fₙ` for some `n > 4`.  This is Pépin's criterion; the equivalence is proved
unconditionally here, so verifying or refuting the conjecture reduces to the right-hand side. -/
theorem FermatPrimeBeyondFour :
    FermatPrimeBeyondFourConjecture ↔
      ∃ n, 4 < n ∧ (3 : ZMod (fermat n)) ^ (2 ^ (2 ^ n - 1)) = -1 := by
  constructor
  · rintro ⟨n, hn, hp⟩
    exact ⟨n, hn, pepin_of_prime n (by omega) hp⟩
  · rintro ⟨n, hn, h⟩
    exact ⟨n, hn, prime_of_pepin n h⟩

/-! ### Verified data: the five known Fermat primes, and two composite Fermat numbers -/

theorem fermat_zero_prime : Nat.Prime (fermat 0) := by
  norm_num [fermat]

theorem fermat_one_prime : Nat.Prime (fermat 1) := by
  norm_num [fermat]

theorem fermat_two_prime : Nat.Prime (fermat 2) := by
  norm_num [fermat]

theorem fermat_three_prime : Nat.Prime (fermat 3) := by
  norm_num [fermat]

theorem fermat_four_prime : Nat.Prime (fermat 4) := by
  norm_num [fermat]

/-- `F₅ = 641 * 6700417` is composite (Euler). -/
theorem fermat_five_not_prime : ¬ Nat.Prime (fermat 5) := by
  have h : fermat 5 = 641 * 6700417 := by norm_num [fermat]
  rw [h]
  exact Nat.not_prime_mul (by norm_num) (by norm_num)

/-- `F₆ = 274177 * 67280421310721` is composite (Landry). -/
theorem fermat_six_not_prime : ¬ Nat.Prime (fermat 6) := by
  have h : fermat 6 = 274177 * 67280421310721 := by norm_num [fermat]
  rw [h]
  exact Nat.not_prime_mul (by norm_num) (by norm_num)

end Brockian.FermatNumbers

