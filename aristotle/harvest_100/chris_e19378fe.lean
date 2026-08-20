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
# Hyperperfect Infinitude
Category: Brockian Conjecture
Target: Brockian.HyperperfectNumbers.HyperperfectInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.HyperperfectNumbers

open Finset

/-- The sum of all divisors of `n`, i.e. `σ₁ n`. -/
def sigmaSum (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

/-- The sum of the divisors of `n` other than `1` and `n` itself. -/
def restrictedSum (n : ℕ) : ℕ := sigmaSum n - n - 1

/-- `n` is `k`-hyperperfect when `n = 1 + k * (σ(n) - n - 1)`, i.e. `n` exceeds by one a
`k`-fold multiple of the sum of its divisors other than `1` and `n`. -/
def IsKHyperperfect (k n : ℕ) : Prop := 1 < n ∧ n = 1 + k * restrictedSum n

/-- `n` is hyperperfect when it is `k`-hyperperfect for some `k ≥ 1`. (For `k = 1` this is
exactly the notion of a perfect number.) -/
def IsHyperperfect (n : ℕ) : Prop := ∃ k, 1 ≤ k ∧ IsKHyperperfect k n

/-- The partner `p² - p + 1` of a prime `p`, written without truncated subtraction. -/
def partner (p : ℕ) : ℕ := p * (p - 1) + 1

/-- `6` is `1`-hyperperfect (it is perfect). -/
theorem isKHyperperfect_one_six : IsKHyperperfect 1 6 := by
  refine ⟨by norm_num, ?_⟩
  simp only [restrictedSum, sigmaSum]
  decide

/-- `21` is `2`-hyperperfect. -/
theorem isKHyperperfect_two_twentyone : IsKHyperperfect 2 21 := by
  refine ⟨by norm_num, ?_⟩
  simp only [restrictedSum, sigmaSum]
  decide

/-- `301` is `6`-hyperperfect. -/
theorem isKHyperperfect_six_threehundredone : IsKHyperperfect 6 301 := by
  refine ⟨by norm_num, ?_⟩
  simp only [restrictedSum, sigmaSum]
  decide

/-- Characterisation: for `n > 1`, `n` is hyperperfect exactly when the sum of its divisors
other than `1` and `n` is positive (i.e. `n` is composite) and divides `n - 1`. -/
theorem isHyperperfect_iff {n : ℕ} (hn : 1 < n) :
    IsHyperperfect n ↔ 0 < restrictedSum n ∧ restrictedSum n ∣ (n - 1) := by
  constructor
  · rintro ⟨k, hk, -, hkn⟩
    have hr : 0 < restrictedSum n := by
      rcases Nat.eq_zero_or_pos (restrictedSum n) with h | h
      · rw [h] at hkn; omega
      · exact h
    exact ⟨hr, ⟨k, by rw [Nat.mul_comm]; omega⟩⟩
  · rintro ⟨hr, m, hm⟩
    refine ⟨m, ?_, hn, ?_⟩
    · rcases Nat.eq_zero_or_pos m with rfl | h
      · omega
      · exact h
    · rw [Nat.mul_comm]; omega

theorem sigmaSum_prime {p : ℕ} (hp : p.Prime) : sigmaSum p = 1 + p := by
  rw [sigmaSum, hp.divisors, Finset.sum_pair hp.one_lt.ne]

theorem sigmaSum_mul_of_coprime {a b : ℕ} (h : Nat.Coprime a b) :
    sigmaSum (a * b) = sigmaSum a * sigmaSum b := by
  simpa [sigmaSum] using Nat.Coprime.sum_divisors_mul h

/-- For distinct primes `p, q`, the sum of the divisors of `p * q` other than `1` and `p * q`
is `p + q`. -/
theorem restrictedSum_mul_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    restrictedSum (p * q) = p + q := by
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).2 hne
  have hs : sigmaSum (p * q) = (1 + p) * (1 + q) := by
    rw [sigmaSum_mul_of_coprime hcop, sigmaSum_prime hp, sigmaSum_prime hq]
  have hexp : (1 + p) * (1 + q) = (p * q + 1) + (p + q) := by ring
  rw [restrictedSum, hs]
  omega

/-- **The Minoli–Bear family.** If `p` and `q = p² - p + 1` are primes, then `p * q` is
`(p - 1)`-hyperperfect. -/
theorem isKHyperperfect_partner {p : ℕ} (hp : p.Prime) (hq : (partner p).Prime) :
    IsKHyperperfect (p - 1) (p * partner p) := by
  obtain ⟨c, rfl⟩ : ∃ c, p = c + 2 := ⟨p - 2, by have := hp.two_le; omega⟩
  have hc1 : c + 2 - 1 = c + 1 := by omega
  have hpartner : partner (c + 2) = c * c + 3 * c + 3 := by
    rw [partner, hc1]; ring
  have hne : c + 2 ≠ partner (c + 2) := by omega
  refine ⟨?_, ?_⟩
  · rw [hpartner]; nlinarith
  · rw [restrictedSum_mul_primes hp hq hne, hpartner]
    rw [hc1]
    ring

theorem isHyperperfect_partner {p : ℕ} (hp : p.Prime) (hq : (partner p).Prime) :
    IsHyperperfect (p * partner p) := by
  refine ⟨p - 1, ?_, isKHyperperfect_partner hp hq⟩
  have := hp.two_le
  omega

/-- **Hyperperfect Infinitude (conditional).** If there are infinitely many primes `p` for which
`p² - p + 1` is also prime (a Bunyakovsky/Schinzel-type hypothesis for the polynomial
`x² - x + 1`, beyond current unconditional methods), then there are infinitely many
hyperperfect numbers.

Each such `p` yields the hyperperfect number `p * (p² - p + 1)`, which is
`(p - 1)`-hyperperfect. -/
theorem HyperperfectInfinitude
    (h : {p : ℕ | p.Prime ∧ (partner p).Prime}.Infinite) :
    {n : ℕ | IsHyperperfect n}.Infinite := by
  refine Set.infinite_of_forall_exists_gt (fun a => ?_)
  obtain ⟨p, ⟨hp, hq⟩, hpa⟩ := h.exists_gt a
  refine ⟨p * partner p, isHyperperfect_partner hp hq, ?_⟩
  have h1 : 1 ≤ partner p := by simp [partner]
  calc a < p := hpa
    _ ≤ p * partner p := Nat.le_mul_of_pos_right p h1

end Brockian.HyperperfectNumbers

