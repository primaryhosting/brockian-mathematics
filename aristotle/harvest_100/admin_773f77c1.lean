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

import Mathlib

/-!
# Woodall Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.CullenWoodall.WoodallPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.CullenWoodall

/-- The `n`-th Woodall number `W n = n * 2 ^ n - 1` (natural subtraction; harmless
since `n * 2 ^ n ≥ 1` for `n ≥ 1`). -/
def woodall (n : ℕ) : ℕ := n * 2 ^ n - 1

/-- A *Woodall prime* is a prime of the form `n * 2 ^ n - 1` with `n ≥ 1`. -/
def IsWoodallPrime (p : ℕ) : Prop := p.Prime ∧ ∃ n, 1 ≤ n ∧ woodall n = p

/-- The set of Woodall primes. -/
def woodallPrimes : Set ℕ := {p | IsWoodallPrime p}

/-- The set of indices `n ≥ 1` for which the Woodall number `W n` is prime. -/
def woodallIndices : Set ℕ := {n | 1 ≤ n ∧ (woodall n).Prime}

/-! ## Basic arithmetic of Woodall numbers -/

lemma one_le_mul_two_pow {n : ℕ} (hn : 1 ≤ n) : 1 ≤ n * 2 ^ n :=
  Nat.one_le_iff_ne_zero.2 (by positivity)

lemma woodall_add_one {n : ℕ} (hn : 1 ≤ n) : woodall n + 1 = n * 2 ^ n := by
  have := one_le_mul_two_pow hn
  simp only [woodall]
  omega

/-- On `n ≥ 1` the Woodall numbers are strictly increasing. -/
lemma woodall_lt_woodall {m n : ℕ} (hm : 1 ≤ m) (hmn : m < n) : woodall m < woodall n := by
  have hpow : (2 : ℕ) ^ m ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hmn.le
  have h1 : m * 2 ^ m < n * 2 ^ n :=
    lt_of_lt_of_le (by
        have : (0 : ℕ) < 2 ^ m := Nat.two_pow_pos m
        exact Nat.mul_lt_mul_of_lt_of_le hmn (le_refl _) this)
      (Nat.mul_le_mul_left n hpow)
  have hm1 : 1 ≤ m * 2 ^ m := one_le_mul_two_pow hm
  simp only [woodall]
  omega

lemma woodall_injOn : Set.InjOn woodall {n | 1 ≤ n} := by
  intro m hm n hn h
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact absurd h (woodall_lt_woodall hm hlt).ne
  · exact absurd h.symm (woodall_lt_woodall hn hlt).ne

lemma le_woodall {n : ℕ} (hn : 1 ≤ n) : n ≤ woodall n := by
  have h : n * 2 ≤ n * 2 ^ n := by
    have h2 : (2 : ℕ) ^ 1 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    simpa using Nat.mul_le_mul_left n h2
  simp only [woodall]
  omega

/-! ## Small Woodall primes -/

lemma woodall_two : woodall 2 = 7 := by decide
lemma woodall_three : woodall 3 = 23 := by decide
lemma woodall_six : woodall 6 = 383 := by decide

lemma isWoodallPrime_seven : IsWoodallPrime 7 := ⟨by norm_num, 2, by norm_num, woodall_two⟩
lemma isWoodallPrime_twentyThree : IsWoodallPrime 23 :=
  ⟨by norm_num, 3, by norm_num, woodall_three⟩
lemma isWoodallPrime_383 : IsWoodallPrime 383 := ⟨by norm_num, 6, by norm_num, woodall_six⟩

/-- The set of Woodall primes is nonempty. -/
theorem woodallPrimes_nonempty : woodallPrimes.Nonempty := ⟨7, isWoodallPrime_seven⟩

/-! ## Infinitely many composite Woodall numbers -/

lemma two_pow_mod_three (n : ℕ) : 2 ^ n % 3 = if n % 2 = 0 then 1 else 2 := by
  induction n with
  | zero => rfl
  | succ k ih =>
      have hstep : 2 ^ (k + 1) % 3 = (2 * (2 ^ k % 3)) % 3 := by
        rw [pow_succ]
        omega
      rw [hstep, ih]
      rcases Nat.even_or_odd k with hk | hk
      · have h0 : k % 2 = 0 := Nat.even_iff.1 hk
        rw [if_pos h0, if_neg (by omega)]
      · have h1 : k % 2 = 1 := Nat.odd_iff.1 hk
        rw [if_neg (by omega), if_pos (by omega)]

/-- If `n ≡ 4` or `n ≡ 5 (mod 6)` then `3 ∣ W n`. -/
lemma three_dvd_woodall {n : ℕ} (hn : n % 6 = 4 ∨ n % 6 = 5) : 3 ∣ woodall n := by
  have hn1 : 1 ≤ n := by omega
  have hpow : 2 ^ n % 3 = if n % 2 = 0 then 1 else 2 := two_pow_mod_three n
  have hmul : n * 2 ^ n % 3 = (n % 3) * (2 ^ n % 3) % 3 := Nat.mul_mod _ _ _
  have hW : woodall n + 1 = n * 2 ^ n := woodall_add_one hn1
  rcases hn with h | h
  · have h2 : n % 2 = 0 := by omega
    have h3 : n % 3 = 1 := by omega
    rw [if_pos h2] at hpow
    rw [hpow, h3] at hmul
    omega
  · have h3 : n % 3 = 2 := by omega
    rw [if_neg (by omega)] at hpow
    rw [hpow, h3] at hmul
    omega

/-- Woodall numbers with index `≡ 4, 5 (mod 6)` are composite (not prime). -/
theorem woodall_not_prime_of_mod_six {n : ℕ} (hn : n % 6 = 4 ∨ n % 6 = 5) :
    ¬ (woodall n).Prime := by
  intro hp
  have hdvd : 3 ∣ woodall n := three_dvd_woodall hn
  have hle : n ≤ woodall n := le_woodall (by omega)
  have hlt : 3 < woodall n := by omega
  rcases hp.eq_one_or_self_of_dvd 3 hdvd with h | h <;> omega

/-- There are infinitely many composite Woodall numbers. -/
theorem infinite_composite_woodall : {n : ℕ | 1 ≤ n ∧ ¬ (woodall n).Prime}.Infinite := by
  apply Set.Infinite.mono (s := Set.range (fun k : ℕ => 6 * k + 4))
  · rintro _ ⟨k, rfl⟩
    show 1 ≤ 6 * k + 4 ∧ ¬ (woodall (6 * k + 4)).Prime
    exact ⟨by omega, woodall_not_prime_of_mod_six (Or.inl (by omega))⟩
  · exact Set.infinite_range_of_injective (fun a b h => by
      have h' : 6 * a + 4 = 6 * b + 4 := h
      omega)

/-! ## Reduction of the conjecture to the set of indices -/

/-- **Woodall prime infinitude (Lean-checked reduction).**  The infinitude of the set of
Woodall primes is *equivalent* to the infinitude of the set of indices `n ≥ 1` for which
`n * 2 ^ n - 1` is prime.  (The unconditional infinitude of Woodall primes is an open
problem; what is proved here is this reduction.) -/
theorem WoodallPrimeInfinitude : woodallPrimes.Infinite ↔ woodallIndices.Infinite := by
  constructor
  · intro h
    have hsub : woodallPrimes ⊆ woodall '' woodallIndices := by
      rintro p ⟨hp, n, hn, rfl⟩
      exact ⟨n, ⟨hn, hp⟩, rfl⟩
    exact Set.Infinite.of_image woodall (h.mono hsub)
  · intro h
    have hsub : woodall '' woodallIndices ⊆ woodallPrimes := by
      rintro _ ⟨n, ⟨hn, hp⟩, rfl⟩
      exact ⟨hp, n, hn, rfl⟩
    exact Set.Infinite.mono hsub (h.image (woodall_injOn.mono (fun n hn => hn.1)))

/-- A convenient equivalent form of the conjecture: for every bound `N` there is an index
`n > N` with `n * 2 ^ n - 1` prime. -/
theorem woodallPrimeInfinitude_iff_unbounded :
    woodallPrimes.Infinite ↔ ∀ N : ℕ, ∃ n, N < n ∧ (woodall n).Prime := by
  rw [WoodallPrimeInfinitude]
  constructor
  · intro h N
    obtain ⟨n, hn, hgt⟩ := h.exists_gt N
    exact ⟨n, hgt, hn.2⟩
  · intro h
    apply Set.infinite_of_not_bddAbove
    rintro ⟨N, hN⟩
    obtain ⟨n, hgt, hp⟩ := h N
    exact absurd (hN ⟨by omega, hp⟩) (by omega)

end Brockian.CullenWoodall

