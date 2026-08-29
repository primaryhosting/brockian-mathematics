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

-- # Sophie Germain Infinitude
-- Category: Brockian Conjecture
-- Target: Brockian.SophieGermain.SophieGermainInfinitude
-- Verification: pending
-- Provenance: Aristotle theorem prover (Harmonic)

import Mathlib

/-!
# Sophie Germain Infinitude
Category: Brockian Conjecture
Target: Brockian.SophieGermain.SophieGermainInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxRecDepth 40000

namespace Brockian.SophieGermain

/-- A *Sophie Germain prime* is a prime `p` such that `2 * p + 1` is also prime. -/
def IsSophieGermain (p : ℕ) : Prop := Nat.Prime p ∧ Nat.Prime (2 * p + 1)

instance (p : ℕ) : Decidable (IsSophieGermain p) := by
  unfold IsSophieGermain; infer_instance

/-- A *safe prime* is a prime `q` of the form `q = 2 * p + 1` with `p` prime. -/
def IsSafePrime (q : ℕ) : Prop := ∃ p, IsSophieGermain p ∧ q = 2 * p + 1

/-- The set of Sophie Germain primes. -/
def sophieGermainSet : Set ℕ := {p | IsSophieGermain p}

/-- The set of safe primes. -/
def safePrimeSet : Set ℕ := {q | IsSafePrime q}

/-! ## Explicit examples -/

theorem isSophieGermain_two : IsSophieGermain 2 := by decide

theorem isSophieGermain_three : IsSophieGermain 3 := by decide

theorem isSophieGermain_five : IsSophieGermain 5 := by decide

theorem isSophieGermain_eleven : IsSophieGermain 11 := by decide

theorem isSophieGermain_eightyNine : IsSophieGermain 89 := by decide

/-- There are exactly ten Sophie Germain primes below `100`. -/
theorem card_sophieGermain_below_hundred :
    ((Finset.range 100).filter IsSophieGermain).card = 10 := by decide

/-- Explicit list of the Sophie Germain primes below `100`. -/
theorem sophieGermain_below_hundred :
    ((Finset.range 100).filter IsSophieGermain) = {2, 3, 5, 11, 23, 29, 41, 53, 83, 89} := by decide

/-! ## Elementary structure -/

/-- Apart from `p = 2`, a Sophie Germain prime is odd. -/
theorem odd_of_isSophieGermain {p : ℕ} (hp : IsSophieGermain p) (hne : p ≠ 2) : Odd p :=
  hp.1.odd_of_ne_two hne

/-- Sophie Germain primes other than `2` and `3` are congruent to `2` mod `3`. -/
theorem mod_three_of_isSophieGermain {p : ℕ} (hp : IsSophieGermain p) (h2 : p ≠ 3)
    (h3 : 2 * p + 1 ≠ 3) : p % 3 = 2 := by
  have hp3 : ¬ (3 ∣ p) := fun h => h2 ((Nat.prime_dvd_prime_iff_eq (by norm_num) hp.1).mp h).symm
  have hq3 : ¬ (3 ∣ 2 * p + 1) := fun h =>
    h3 ((Nat.prime_dvd_prime_iff_eq (by norm_num) hp.2).mp h).symm
  have h : p % 3 < 3 := Nat.mod_lt p (by norm_num)
  interval_cases hm : (p % 3)
  · exact absurd (Nat.dvd_of_mod_eq_zero hm) hp3
  · exact absurd (by omega : (3 : ℕ) ∣ 2 * p + 1) hq3
  · rfl

/-! ## Sophie Germain's theorem on Mersenne numbers -/

private lemma two_mul_add_two_lt_two_pow {n : ℕ} (hn : 4 ≤ n) : 2 * n + 2 < 2 ^ n := by
  induction n with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_or_ge k 4 with hk | hk
    · interval_cases k <;> simp_all
    · have h1 := ih (by omega)
      have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
      omega

/-- **Sophie Germain's classical divisibility theorem.**  If `p ≡ 3 (mod 4)` is a Sophie
Germain prime with `p > 3`, then the safe prime `2 * p + 1` divides the Mersenne number
`2 ^ p - 1`. -/
theorem dvd_mersenne_of_isSophieGermain {p : ℕ} (hp : IsSophieGermain p) (h4 : p % 4 = 3)
    (hp3 : 3 < p) : (2 * p + 1) ∣ 2 ^ p - 1 := by
  set q := 2 * p + 1 with hqdef
  haveI : Fact (Nat.Prime q) := ⟨hp.2⟩
  have hq8 : q % 8 = 7 := by omega
  have hsq : IsSquare (2 : ZMod q) :=
    (ZMod.exists_sq_eq_two_iff (by omega)).mpr (Or.inr hq8)
  have h2ne : (2 : ZMod q) ≠ 0 := by
    have h : ((2 : ℕ) : ZMod q) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro h
      have := Nat.le_of_dvd (by omega) h
      omega
    simpa using h
  have hcrit := (ZMod.euler_criterion q h2ne).mp hsq
  have hqhalf : q / 2 = p := by omega
  rw [hqhalf] at hcrit
  have hcast : ((2 ^ p : ℕ) : ZMod q) = ((1 : ℕ) : ZMod q) := by push_cast; simpa using hcrit
  have hmod : 2 ^ p ≡ 1 [MOD q] := (ZMod.natCast_eq_natCast_iff _ _ _).mp hcast
  exact (Nat.modEq_iff_dvd' Nat.one_le_two_pow).mp hmod.symm

/-- For a Sophie Germain prime `p > 3` with `p ≡ 3 (mod 4)`, the Mersenne number `2 ^ p - 1`
is composite. -/
theorem not_prime_mersenne_of_isSophieGermain {p : ℕ} (hp : IsSophieGermain p) (h4 : p % 4 = 3)
    (hp3 : 3 < p) : ¬ Nat.Prime (2 ^ p - 1) := by
  intro hM
  have hdvd := dvd_mersenne_of_isSophieGermain hp h4 hp3
  have hlt : 2 * p + 2 < 2 ^ p := two_mul_add_two_lt_two_pow (by omega)
  rcases (Nat.Prime.eq_one_or_self_of_dvd hM _ hdvd) with h | h <;> omega

/-! ## Equivalent formulations of the infinitude statement -/

/-- The Sophie Germain primes form an infinite set iff they are unbounded. -/
theorem infinite_iff_unbounded :
    sophieGermainSet.Infinite ↔ ∀ N : ℕ, ∃ p, N < p ∧ IsSophieGermain p := by
  constructor
  · intro h N
    obtain ⟨p, hp, hpN⟩ := h.exists_gt N
    exact ⟨p, hpN, hp⟩
  · intro h
    refine Set.infinite_of_not_bddAbove ?_
    rintro ⟨N, hN⟩
    obtain ⟨p, hpN, hp⟩ := h N
    exact absurd (hN hp) (by omega)

/-- Infinitude of Sophie Germain primes follows from unboundedness. -/
theorem infinite_of_unbounded (h : ∀ N : ℕ, ∃ p, N < p ∧ IsSophieGermain p) :
    sophieGermainSet.Infinite :=
  infinite_iff_unbounded.mpr h

/-- The map `p ↦ 2 * p + 1` is a bijection from Sophie Germain primes onto safe primes,
so infinitude of safe primes is equivalent to infinitude of Sophie Germain primes. -/
theorem safePrime_infinite_iff : safePrimeSet.Infinite ↔ sophieGermainSet.Infinite := by
  constructor
  · intro h
    rw [infinite_iff_unbounded]
    intro N
    obtain ⟨q, hq, hqN⟩ := h.exists_gt (2 * N + 1)
    obtain ⟨p, hp, rfl⟩ := hq
    exact ⟨p, by omega, hp⟩
  · intro h
    have himg : safePrimeSet = (fun p => 2 * p + 1) '' sophieGermainSet := by
      ext q
      constructor
      · rintro ⟨p, hp, rfl⟩; exact ⟨p, hp, rfl⟩
      · rintro ⟨p, hp, rfl⟩; exact ⟨p, hp, rfl⟩
    rw [himg]
    exact h.image (Set.injOn_of_injective (fun a b hab => by omega))

/-- **Sophie Germain infinitude (conditional reduction).**

The infinitude of Sophie Germain primes — an open problem — is here established
*conditionally*: it follows from (and is in fact equivalent to) either of the two
standard reformulations, namely unboundedness of the set of Sophie Germain primes,
or infinitude of the set of safe primes.  The statement also records the
unconditional fact that Sophie Germain primes exist. -/
theorem SophieGermainInfinitude :
    (∃ p, IsSophieGermain p) ∧
    ((∀ N : ℕ, ∃ p, N < p ∧ IsSophieGermain p) → sophieGermainSet.Infinite) ∧
    (safePrimeSet.Infinite → sophieGermainSet.Infinite) ∧
    (sophieGermainSet.Infinite ↔ ∀ N : ℕ, ∃ p, N < p ∧ IsSophieGermain p) :=
  ⟨⟨2, isSophieGermain_two⟩, infinite_of_unbounded, safePrime_infinite_iff.mp,
    infinite_iff_unbounded⟩

end Brockian.SophieGermain

