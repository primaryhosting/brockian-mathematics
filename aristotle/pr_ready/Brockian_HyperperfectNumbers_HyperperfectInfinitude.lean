/-!
# Hyperperfect Infinitude
Category: Brockian Conjecture
Target: Brockian.HyperperfectNumbers.HyperperfectInfinitude
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

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
# Hyperperfect Infinitude
Category: Brockian Conjecture
Target: Brockian.HyperperfectNumbers.HyperperfectInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


/-!
# Hyperperfect Infinitude
Category: Brockian Conjecture
Target: Brockian.HyperperfectNumbers.HyperperfectInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace Brockian.HyperperfectNumbers

/-- `n` is `k`-hyperperfect when `k ≥ 1`, `n > 1` and `n = 1 + k * (σ n - n - 1)`, i.e. `k`
times the sum of the divisors of `n` other than `1` and `n` equals `n - 1`.
The equation is written without truncated subtraction as `n + k * (n + 1) = 1 + k * σ n`. -/
def IsHyperperfect (k n : ℕ) : Prop :=
  1 ≤ k ∧ 1 < n ∧ n + k * (n + 1) = 1 + k * (σ 1 n)

/-- The set of hyperperfect numbers (`k`-hyperperfect for some `k ≥ 1`). -/
def Hyperperfect : Set ℕ := {n | ∃ k, IsHyperperfect k n}

/-- The classical perfect number `6` is `1`-hyperperfect. -/
theorem isHyperperfect_one_six : IsHyperperfect 1 6 :=
  ⟨le_refl 1, by norm_num, by decide⟩

/-- `21` is `2`-hyperperfect. -/
theorem isHyperperfect_two_twentyone : IsHyperperfect 2 21 :=
  ⟨by norm_num, by norm_num, by decide⟩

/-- `301 = 7 * 43` is `6`-hyperperfect. -/
theorem isHyperperfect_six_301 : IsHyperperfect 6 301 :=
  ⟨by norm_num, by norm_num, by decide⟩

/-- The sum-of-divisors function on a product of two distinct primes. -/
theorem sigma_one_mul_of_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    σ 1 (p * q) = (p + 1) * (q + 1) := by
  have hmul := (isMultiplicative_sigma (k := 1) :
      ArithmeticFunction.IsMultiplicative (σ 1 : ArithmeticFunction ℕ)).map_mul_of_coprime
      ((Nat.coprime_primes hp hq).mpr hpq)
  rw [hmul, sigma_one_apply, sigma_one_apply, hp.sum_divisors, hq.sum_divisors]

/-- **Key lemma.** If `p` and `q = p² - p + 1` are both prime, then `n = p * q` is
`(p-1)`-hyperperfect. (For `p = 2` this gives the perfect number `6`, for `p = 3` the
`2`-hyperperfect number `21`, for `p = 7` the `6`-hyperperfect number `301`.) -/
theorem isHyperperfect_mul_of_prime {p : ℕ} (hp : p.Prime) (hq : (p ^ 2 - p + 1).Prime) :
    IsHyperperfect (p - 1) (p * (p ^ 2 - p + 1)) := by
  obtain ⟨a, rfl⟩ : ∃ a, p = a + 2 := ⟨p - 2, by have := hp.two_le; omega⟩
  have hsq : (a + 2) ^ 2 = a ^ 2 + 4 * a + 4 := by ring
  have hq' : (a + 2) ^ 2 - (a + 2) + 1 = a ^ 2 + 3 * a + 3 := by omega
  rw [hq'] at hq ⊢
  have hlt : a + 2 < a ^ 2 + 3 * a + 3 := by nlinarith [sq_nonneg a]
  have hne : a + 2 ≠ a ^ 2 + 3 * a + 3 := by omega
  refine ⟨by omega, ?_, ?_⟩
  · nlinarith [sq_nonneg a]
  · rw [sigma_one_mul_of_primes hp hq hne]
    have hk : a + 2 - 1 = a + 1 := by omega
    rw [hk]
    ring

/-- Each such `p * q` is at least `p`, so the family is unbounded. -/
theorem le_mul_of_prime {p : ℕ} (hp : p.Prime) : p ≤ p * (p ^ 2 - p + 1) := by
  have h2 := hp.two_le
  have h1 : 1 ≤ p ^ 2 - p + 1 := by omega
  nlinarith

/-- **Conditional reduction for the Brockian hyperperfect infinitude conjecture.**

If there are infinitely many primes `p` for which `p² - p + 1` is also prime, then there are
infinitely many hyperperfect numbers: indeed each such `p` produces the `(p-1)`-hyperperfect
number `p * (p² - p + 1)`. -/
theorem HyperperfectInfinitude
    (h : {p : ℕ | p.Prime ∧ (p ^ 2 - p + 1).Prime}.Infinite) :
    Hyperperfect.Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨N, hN⟩
  obtain ⟨p, ⟨hp, hq⟩, hpN⟩ := h.exists_gt N
  have hmem : p * (p ^ 2 - p + 1) ∈ Hyperperfect :=
    ⟨p - 1, isHyperperfect_mul_of_prime hp hq⟩
  have h1 := hN hmem
  have h2 := le_mul_of_prime hp
  omega

end Brockian.HyperperfectNumbers

