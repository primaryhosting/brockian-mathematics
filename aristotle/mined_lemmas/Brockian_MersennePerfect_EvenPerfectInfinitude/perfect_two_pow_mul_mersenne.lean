import Brockian.MersennePerfect

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
# Even Perfect Infinitude
Category: Brockian Conjecture
Target: Brockian.MersennePerfect.EvenPerfectInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: written as a plain block comment rather than a module docstring, since Lean 4
requires `import` commands to precede any module docstring.)
-/

import Mathlib

namespace Brockian.MersennePerfect

open Finset

/-- The set of exponents `p` for which the Mersenne number `2 ^ p - 1` is prime. -/

theorem perfect_two_pow_mul_mersenne {k : ℕ} (h : (mersenne (k + 1)).Prime) :
    Nat.Perfect (2 ^ k * mersenne (k + 1)) := by
  set q := mersenne (k + 1) with hq
  have hqpos : 0 < q := h.pos
  have hpos : 0 < 2 ^ k * q := Nat.mul_pos (Nat.two_pow_pos k) hqpos
  have hcop : Nat.Coprime (2 ^ k) q :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr (mersenne_succ_odd k))
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul hpos]
  have hsum : ∑ i ∈ (2 ^ k * q).divisors, i
      = (∑ i ∈ (2 ^ k : ℕ).divisors, i) * (∑ i ∈ q.divisors, i) := by
    have := (ArithmeticFunction.isMultiplicative_sigma (k := 1)).map_mul_of_coprime hcop
    simpa [ArithmeticFunction.sigma_one_apply] using this
  have h1 : ∑ i ∈ (2 ^ k : ℕ).divisors, i = 2 ^ (k + 1) - 1 := by
    rw [Nat.sum_divisors_prime_pow Nat.prime_two, sum_range_two_pow]
  have h2 : ∑ i ∈ q.divisors, i = q + 1 := by
    rw [h.divisors]
    rw [Finset.sum_pair h.one_lt.ne]
    omega
  have hq1 : q + 1 = 2 ^ (k + 1) := by
    have : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
    simp only [hq, mersenne]
    omega
  rw [hsum, h1, h2, hq1]
  have hqval : q = 2 ^ (k + 1) - 1 := rfl
  have hle : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
  have : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
  rw [hqval]
  cases Nat.exists_eq_add_of_le hle with
  | intro c hc =>
    rw [this] at hc ⊢
    nlinarith [hc]

/-- If the Mersenne prime exponent `p` is at least `1`, the associated Euclid number
`2 ^ (p-1) * (2 ^ p - 1)` is even. -/
