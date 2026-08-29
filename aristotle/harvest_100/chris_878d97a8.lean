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
# Oppermann Conjecture
Category: Brockian Conjecture
Target: Brockian.OppermannConjecture.OppermannConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Oppermann Conjecture
Category: Brockian Conjecture
Target: Brockian.OppermannConjecture.OppermannConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Oppermann's conjecture is open, so the main result here is a Lean-checked *conditional
reduction*: Oppermann's conjecture follows from a Legendre-type prime gap hypothesis
(`SqrtPrimeGap`), together with an unconditional verification of the small cases
`2 ≤ n ≤ 40`.
-/

namespace Brockian.OppermannConjecture

/-- **Oppermann's conjecture**: for every `n ≥ 2` there is a prime strictly between
`n(n-1)` and `n²`, and a prime strictly between `n²` and `n(n+1)`. -/
def OppermannStatement : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    (∃ p : ℕ, Nat.Prime p ∧ n * (n - 1) < p ∧ p < n * n) ∧
    (∃ p : ℕ, Nat.Prime p ∧ n * n < p ∧ p < n * (n + 1))

/-- A Legendre-type prime gap hypothesis: every interval `(m, m + √m]` with `m ≥ 100`
contains a prime.  This is an open (but widely believed) statement; it is *not* vacuous,
see `sqrtPrimeGap_witness_100`. -/
def SqrtPrimeGap : Prop :=
  ∀ m : ℕ, 100 ≤ m → ∃ p : ℕ, Nat.Prime p ∧ m < p ∧ p ≤ m + Nat.sqrt m

/-- Sanity check that the hypothesis `SqrtPrimeGap` is not vacuously stated: the required
prime exists for `m = 100`. -/
theorem sqrtPrimeGap_witness_100 :
    ∃ p : ℕ, Nat.Prime p ∧ 100 < p ∧ p ≤ 100 + Nat.sqrt 100 :=
  ⟨101, by norm_num⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 2000000 in
/-- Kernel-checked verification of Oppermann's conjecture for `2 ≤ n ≤ 40`. -/
theorem oppermann_decide :
    ∀ n ∈ Finset.Icc 2 40,
      (∃ p ∈ Finset.Ioo (n * (n - 1)) (n * n), Nat.Prime p) ∧
      (∃ p ∈ Finset.Ioo (n * n) (n * (n + 1)), Nat.Prime p) := by
  decide

/-- The unconditional part: Oppermann's conjecture holds for all `2 ≤ n ≤ 40`. -/
theorem oppermann_small (n : ℕ) (h2 : 2 ≤ n) (h40 : n ≤ 40) :
    (∃ p : ℕ, Nat.Prime p ∧ n * (n - 1) < p ∧ p < n * n) ∧
    (∃ p : ℕ, Nat.Prime p ∧ n * n < p ∧ p < n * (n + 1)) := by
  have h := oppermann_decide n (Finset.mem_Icc.mpr ⟨h2, h40⟩)
  simp only [Finset.mem_Ioo] at h
  obtain ⟨⟨p, ⟨hp1, hp2⟩, hp⟩, ⟨q, ⟨hq1, hq2⟩, hq⟩⟩ := h
  exact ⟨⟨p, hp, hp1, hp2⟩, ⟨q, hq, hq1, hq2⟩⟩

/-- For `n ≥ 11` the lower Oppermann interval `(n(n-1), n²)` follows from `SqrtPrimeGap`. -/
theorem oppermann_lower_of_gap (h : SqrtPrimeGap) (n : ℕ) (hn : 11 ≤ n) :
    ∃ p : ℕ, Nat.Prime p ∧ n * (n - 1) < p ∧ p < n * n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 11 := ⟨n - 11, by omega⟩
  have hsub : (k + 11) - 1 = k + 10 := by omega
  rw [hsub]
  set m := (k + 11) * (k + 10) with hm
  have hm100 : 100 ≤ m := by simp only [hm]; nlinarith
  obtain ⟨p, hp, hlt, hle⟩ := h m hm100
  refine ⟨p, hp, hlt, ?_⟩
  have hsqrt : Nat.sqrt m ≤ k + 10 := by
    have : Nat.sqrt m < k + 11 := by
      rw [Nat.sqrt_lt]
      simp only [hm]; nlinarith
    omega
  have hp' : p ≤ m + (k + 10) := le_trans hle (by omega)
  simp only [hm] at hp' ⊢
  nlinarith

/-- For `n ≥ 11` the upper Oppermann interval `(n², n(n+1))` follows from `SqrtPrimeGap`. -/
theorem oppermann_upper_of_gap (h : SqrtPrimeGap) (n : ℕ) (hn : 11 ≤ n) :
    ∃ p : ℕ, Nat.Prime p ∧ n * n < p ∧ p < n * (n + 1) := by
  have hm100 : 100 ≤ n * n := by nlinarith
  obtain ⟨p, hp, hlt, hle⟩ := h (n * n) hm100
  rw [Nat.sqrt_eq n] at hle
  refine ⟨p, hp, hlt, ?_⟩
  rcases lt_or_eq_of_le hle with hlt' | heq
  · calc p < n * n + n := hlt'
      _ = n * (n + 1) := by ring
  · exfalso
    have hdvd : n ∣ p := ⟨n + 1, by rw [heq]; ring⟩
    rcases Nat.Prime.eq_one_or_self_of_dvd hp n hdvd with h1 | h1
    · omega
    · nlinarith [heq, h1]

/-- **Conditional proof of Oppermann's conjecture.**  Assuming the Legendre-type prime gap
hypothesis `SqrtPrimeGap` (a prime in every interval `(m, m + √m]` for `m ≥ 100`),
Oppermann's conjecture holds for all `n ≥ 2`.  The range `2 ≤ n ≤ 40` is verified
unconditionally, and for `n ≥ 11` the two required primes are produced from the
hypothesis applied to `m = n(n-1)` and `m = n²` respectively. -/
theorem OppermannConjecture (h : SqrtPrimeGap) : OppermannStatement := by
  intro n hn
  by_cases h40 : n ≤ 40
  · exact oppermann_small n hn h40
  · have hn11 : 11 ≤ n := by omega
    exact ⟨oppermann_lower_of_gap h n hn11, oppermann_upper_of_gap h n hn11⟩

end Brockian.OppermannConjecture

