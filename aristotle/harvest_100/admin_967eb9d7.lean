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

import Mathlib

/-!
# Woodall Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.CullenWoodall.WoodallPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


namespace Brockian.CullenWoodall

/-- The `n`-th Woodall number `W n = n * 2 ^ n - 1` (natural subtraction; `W 0 = 0`). -/
def woodall (n : ℕ) : ℕ := n * 2 ^ n - 1

/-- The set of Woodall primes, as a set of primes. -/
def woodallPrimes : Set ℕ := {p | p.Prime ∧ ∃ n, woodall n = p}

/-- The index set of Woodall primes. -/
def woodallPrimeIndices : Set ℕ := {n | (woodall n).Prime}

/-- The Woodall prime conjecture: there are infinitely many Woodall primes.
This is an open problem; below we prove unconditional partial results
together with a conditional reduction. -/
def WoodallConjecture : Prop := woodallPrimes.Infinite

/-! ### Basic arithmetic of Woodall numbers -/

lemma woodall_zero : woodall 0 = 0 := rfl

lemma one_le_mul_two_pow {n : ℕ} (hn : 1 ≤ n) : 1 ≤ n * 2 ^ n := by
  have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  exact Nat.one_le_iff_ne_zero.mpr (by positivity)

lemma woodall_succ_lt (n : ℕ) : woodall n < woodall (n + 1) := by
  have h : n * 2 ^ n + 2 ≤ (n + 1) * 2 ^ (n + 1) := by
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have h2 : (n + 1) * 2 ^ (n + 1) = n * 2 ^ n + (n + 2) * 2 ^ n := by ring
    nlinarith
  simp only [woodall]
  omega

lemma woodall_strictMono : StrictMono woodall :=
  strictMono_nat_of_lt_succ woodall_succ_lt

lemma woodall_injective : Function.Injective woodall := woodall_strictMono.injective

lemma le_woodall (n : ℕ) : n ≤ woodall n := woodall_strictMono.le_apply

/-! ### Reduction: the two natural formulations agree -/

/-- The set of Woodall primes is the image of the index set under `woodall`. -/
lemma woodallPrimes_eq_image : woodallPrimes = woodall '' woodallPrimeIndices := by
  ext p
  constructor
  · rintro ⟨hp, n, rfl⟩
    exact ⟨n, hp, rfl⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨hn, n, rfl⟩

/-- Infinitude of Woodall primes is equivalent to infinitude of their index set. -/
theorem woodallPrimes_infinite_iff_indices_infinite :
    woodallPrimes.Infinite ↔ woodallPrimeIndices.Infinite := by
  rw [woodallPrimes_eq_image]
  exact Set.infinite_image_iff woodall_injective.injOn

/-- Infinitude of Woodall primes is equivalent to the index set being unbounded. -/
theorem woodallPrimes_infinite_iff_unbounded :
    woodallPrimes.Infinite ↔ ∀ N : ℕ, ∃ n > N, (woodall n).Prime := by
  rw [woodallPrimes_infinite_iff_indices_infinite]
  constructor
  · intro h N
    obtain ⟨n, hn, hlt⟩ := h.exists_gt N
    exact ⟨n, hlt, hn⟩
  · intro h
    refine Set.infinite_of_not_bddAbove ?_
    rintro ⟨N, hN⟩
    obtain ⟨n, hn, hp⟩ := h N
    have := hN hp
    omega

/-- **Conditional reduction.** If Woodall primes occur with arbitrarily large index,
then there are infinitely many Woodall primes. (The hypothesis is exactly the open
arithmetic content of the conjecture; the theorem reduces the set-theoretic
statement to it.) -/
theorem WoodallPrimeInfinitude (h : ∀ N : ℕ, ∃ n > N, (woodall n).Prime) :
    WoodallConjecture :=
  woodallPrimes_infinite_iff_unbounded.mpr h

/-! ### Unconditional obstruction modulo 3 -/

lemma sixtyfour_pow_mod_three (q : ℕ) : 64 ^ q % 3 = 1 := by
  rw [Nat.pow_mod]
  simp

/-- If `n ≡ 4` or `n ≡ 5 (mod 6)` then `3 ∣ W n`. -/
theorem three_dvd_woodall (n : ℕ) (hn : n % 6 = 4 ∨ n % 6 = 5) : 3 ∣ woodall n := by
  have key : n * 2 ^ n % 3 = 1 := by
    obtain ⟨q, hq⟩ : ∃ q, n = 6 * q + n % 6 := ⟨n / 6, by omega⟩
    rcases hn with h | h
    · have hn4 : n = 6 * q + 4 := by omega
      subst hn4
      have h2 : (2:ℕ) ^ (6 * q + 4) = 64 ^ q * 16 := by
        rw [pow_add, pow_mul]; norm_num
      rw [h2, Nat.mul_mod, Nat.mul_mod (64 ^ q), sixtyfour_pow_mod_three]
      have h3 : (6 * q + 4) % 3 = 1 := by omega
      rw [h3]
    · have hn5 : n = 6 * q + 5 := by omega
      subst hn5
      have h2 : (2:ℕ) ^ (6 * q + 5) = 64 ^ q * 32 := by
        rw [pow_add, pow_mul]; norm_num
      rw [h2, Nat.mul_mod, Nat.mul_mod (64 ^ q), sixtyfour_pow_mod_three]
      have h3 : (6 * q + 5) % 3 = 2 := by omega
      rw [h3]
  simp only [woodall]
  omega

lemma woodall_ge_of_four_le {n : ℕ} (hn : 4 ≤ n) : 63 ≤ woodall n := by
  have h1 : (16:ℕ) ≤ 2 ^ n := by
    calc (16:ℕ) = 2 ^ 4 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have : 4 * 16 ≤ n * 2 ^ n := Nat.mul_le_mul hn h1
  simp only [woodall]
  omega

/-- Woodall numbers with index `≥ 4` congruent to `4` or `5 (mod 6)` are composite. -/
theorem not_prime_woodall_of_mod_six {n : ℕ} (hn : 4 ≤ n)
    (h : n % 6 = 4 ∨ n % 6 = 5) : ¬ (woodall n).Prime := by
  intro hp
  have hdvd := three_dvd_woodall n h
  have h3 : woodall n = 3 :=
    ((hp.eq_one_or_self_of_dvd 3 hdvd).resolve_left (by norm_num)).symm
  have := woodall_ge_of_four_le hn
  omega

/-- The index of a Woodall prime is never `≡ 4` or `5 (mod 6)` (for indices `≥ 4`). -/
theorem woodall_prime_index_mod_six {n : ℕ} (hn : 4 ≤ n) (hp : (woodall n).Prime) :
    n % 6 = 0 ∨ n % 6 = 1 ∨ n % 6 = 2 ∨ n % 6 = 3 := by
  by_contra h
  exact not_prime_woodall_of_mod_six hn (by omega) hp

/-- There are infinitely many composite Woodall numbers. -/
theorem infinite_composite_woodall : {n : ℕ | ¬ (woodall n).Prime}.Infinite := by
  apply Set.infinite_of_injective_forall_mem (f := fun k : ℕ => 6 * k + 4)
  case hi =>
    intro a b hab
    simp only at hab
    omega
  case hf =>
    intro k
    exact not_prime_woodall_of_mod_six (by omega) (by omega)

/-! ### Divisibility of Woodall numbers by an arbitrary odd prime -/

/-- Reformulation of divisibility of a Woodall number as a congruence. -/
lemma dvd_woodall_iff {p n : ℕ} (hn : 1 ≤ n) :
    p ∣ woodall n ↔ n * 2 ^ n ≡ 1 [MOD p] := by
  have hm : 1 ≤ n * 2 ^ n := one_le_mul_two_pow hn
  constructor
  · intro h
    have h0 : woodall n ≡ 0 [MOD p] := (Nat.modEq_zero_iff_dvd).mpr h
    have := h0.add_right 1
    simpa [woodall, Nat.sub_add_cancel hm] using this
  · intro h
    have h1 : (woodall n) + 1 ≡ 0 + 1 [MOD p] := by
      simpa [woodall, Nat.sub_add_cancel hm] using h
    exact (Nat.modEq_zero_iff_dvd).mp (Nat.ModEq.add_right_cancel' 1 h1)

/-- Divisibility of Woodall numbers by an odd prime `p` is periodic in the index
with period `p * (p - 1)`. -/
theorem dvd_woodall_periodic {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) {n : ℕ} (hn : 1 ≤ n) :
    (p ∣ woodall n ↔ p ∣ woodall (n + p * (p - 1))) := by
  have h2 : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hodd)
  have hferm : (2:ℕ) ^ (p - 1) ≡ 1 [MOD p] := by
    have := Nat.ModEq.pow_totient h2
    rwa [Nat.totient_prime hp] at this
  have hpow : (2:ℕ) ^ (n + p * (p - 1)) ≡ 2 ^ n [MOD p] := by
    calc (2:ℕ) ^ (n + p * (p - 1)) = 2 ^ n * ((2 ^ (p - 1)) ^ p) := by
          rw [pow_add, ← pow_mul, mul_comm p (p - 1)]
      _ ≡ 2 ^ n * 1 ^ p [MOD p] := Nat.ModEq.mul_left _ (hferm.pow p)
      _ = 2 ^ n := by ring
  have hidx : (n + p * (p - 1)) ≡ n [MOD p] := by
    simp [Nat.ModEq, Nat.add_mul_mod_self_left]
  have hmul : (n + p * (p - 1)) * 2 ^ (n + p * (p - 1)) ≡ n * 2 ^ n [MOD p] := hidx.mul hpow
  rw [dvd_woodall_iff hn, dvd_woodall_iff (by omega : 1 ≤ n + p * (p - 1))]
  exact ⟨fun h => hmul.trans h, fun h => hmul.symm.trans h⟩

/-- For every odd prime `p` there is an index `n ≥ 1` with `p ∣ W n`.

The witness is obtained from the Chinese remainder theorem: any `n` with
`n ≡ 1 (mod p-1)` and `n ≡ (p+1)/2 (mod p)` satisfies `n * 2 ^ n ≡ 1 (mod p)`. -/
theorem exists_dvd_woodall {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) :
    ∃ n, 1 ≤ n ∧ p ∣ woodall n := by
  have hp2 : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hodd)
  have hpodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hodd)
  have hcop : Nat.Coprime (p - 1) p := by
    have h1 : Nat.Coprime (p - 1) ((p - 1) + 1) := by simp
    rwa [show (p - 1) + 1 = p by omega] at h1
  obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder hcop 1 ((p + 1) / 2)
  -- `k ≡ 1 [MOD p-1]` and `k ≡ (p+1)/2 [MOD p]`
  have hmod : k % p = (p + 1) / 2 := by
    have hlt : (p + 1) / 2 < p := by omega
    have := hk2
    rwa [Nat.ModEq, Nat.mod_eq_of_lt hlt] at this
  have hkpos : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · simp at hmod; omega
    · exact h
  have hkmod : k % (p - 1) = 1 := by
    have := hk1
    rwa [Nat.ModEq, Nat.mod_eq_of_lt (by omega : 1 < p - 1)] at this
  obtain ⟨t, ht⟩ : ∃ t, k = (p - 1) * t + 1 := by
    refine ⟨k / (p - 1), ?_⟩
    have := Nat.div_add_mod k (p - 1)
    omega
  have hcop2 : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hodd)
  have hferm : (2:ℕ) ^ (p - 1) ≡ 1 [MOD p] := by
    have := Nat.ModEq.pow_totient hcop2
    rwa [Nat.totient_prime hp] at this
  have hpow : (2:ℕ) ^ k ≡ 2 [MOD p] := by
    calc (2:ℕ) ^ k = ((2 ^ (p - 1)) ^ t) * 2 := by rw [← pow_mul, ← pow_succ, ← ht]
      _ ≡ (1 ^ t) * 2 [MOD p] := Nat.ModEq.mul_right 2 (hferm.pow t)
      _ = 2 := by ring
  have hfinal : k * 2 ^ k ≡ 1 [MOD p] := by
    have h1 : k * 2 ^ k ≡ ((p + 1) / 2) * 2 [MOD p] := hk2.mul hpow
    have h2 : ((p + 1) / 2) * 2 = p + 1 := by omega
    have h3 : p + 1 ≡ 0 + 1 [MOD p] := Nat.ModEq.add_right 1 (Nat.modEq_zero_iff_dvd.mpr dvd_rfl)
    rw [h2] at h1
    simpa using h1.trans h3
  exact ⟨k, hkpos, (dvd_woodall_iff hkpos).mpr hfinal⟩

/-- For every odd prime `p` there are infinitely many `n` with `p ∣ W n`. -/
theorem infinite_dvd_woodall {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) :
    {n : ℕ | p ∣ woodall n}.Infinite := by
  obtain ⟨n₀, hn₀, hdvd₀⟩ := exists_dvd_woodall hp hodd
  have hp2 : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hodd)
  set T := p * (p - 1) with hT
  have hTpos : 0 < T := Nat.mul_pos (by omega) (by omega)
  have key : ∀ j : ℕ, 1 ≤ n₀ + j * T ∧ p ∣ woodall (n₀ + j * T) := by
    intro j
    induction j with
    | zero => simpa using ⟨hn₀, hdvd₀⟩
    | succ k ih =>
      obtain ⟨hk1, hk2⟩ := ih
      refine ⟨by nlinarith [hk1], ?_⟩
      have := (dvd_woodall_periodic hp hodd hk1).mp hk2
      have heq : n₀ + k * T + T = n₀ + (k + 1) * T := by ring
      rwa [heq] at this
  apply Set.infinite_of_injective_forall_mem (f := fun j : ℕ => n₀ + j * T)
  case hi =>
    intro a b hab
    simp only at hab
    have : a * T = b * T := by omega
    exact Nat.eq_of_mul_eq_mul_right hTpos this
  case hf =>
    intro j
    exact (key j).2

end Brockian.CullenWoodall

