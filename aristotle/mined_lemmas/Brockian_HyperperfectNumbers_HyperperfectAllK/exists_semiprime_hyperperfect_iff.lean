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
# Hyperperfect All K
Category: Brockian Conjecture
Target: Brockian.HyperperfectNumbers.HyperperfectAllK
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.HyperperfectNumbers

open Finset

/-- `Hyperperfect k n` says that `n` is a *`k`-hyperperfect number*, i.e. `n > 1` and
`n = 1 + k * (σ(n) - n - 1)`, where `σ(n) = ∑ d ∣ n, d`.

The defining equation is written in the subtraction-free form
`(k + 1) * n + k = k * σ(n) + 1`, which over the integers is equivalent to
`n = 1 + k * (σ n - n - 1)`. -/

theorem exists_semiprime_hyperperfect_iff {k : ℕ} :
    (∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ Hyperperfect k (p * q)) ↔
      ∃ d e : ℕ, d * e = k ^ 2 + 1 ∧ (k + d).Prime ∧ (k + e).Prime := by
  constructor
  · rintro ⟨p, q, hp, hq, hpq, hyp⟩
    rw [hyperperfect_mul_primes_iff hp hq hpq] at hyp
    have hkp : k < p := by
      by_contra hc
      have : p * q ≤ k * q := Nat.mul_le_mul_right q (by omega)
      omega
    have hkq : k < q := by
      by_contra hc
      have : p * q ≤ p * k := Nat.mul_le_mul_left p (by omega)
      nlinarith
    obtain ⟨d, rfl⟩ : ∃ d, p = k + d := ⟨p - k, by omega⟩
    obtain ⟨e, rfl⟩ : ∃ e, q = k + e := ⟨q - k, by omega⟩
    exact ⟨d, e, by nlinarith [hyp], hp, hq⟩
  · rintro ⟨d, e, hde, hp, hq⟩
    have hne : d ≠ e := by
      rintro rfl
      rcases Nat.lt_or_ge d (k + 1) with h | h
      · nlinarith [hp.two_le, hq.two_le]
      · nlinarith [hp.two_le, hq.two_le]
    refine ⟨k + d, k + e, hp, hq, by omega, ?_⟩
    rw [hyperperfect_mul_primes_iff hp hq (by omega)]
    nlinarith [hde]

/-- The condition, for each `k ≥ 1`, that `k ^ 2 + 1` admits a factorisation `d * e`
with both `k + d` and `k + e` prime. -/
