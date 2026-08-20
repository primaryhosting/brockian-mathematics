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
# Goldbach Covariance Transfer
Category: Brockian Conjecture
Target: Brockian.GoldbachComb.GoldbachCovarianceTransfer
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Goldbach Covariance Transfer
Category: Brockian Conjecture
Target: Brockian.GoldbachComb.GoldbachCovarianceTransfer
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.GoldbachComb

open Finset

/-- `goldbachCount n` is the number of ordered Goldbach representations of `n`, i.e. the
number of primes `p ≤ n` such that `n - p` is also prime. -/

theorem cov_affine (S : Finset ℕ) (f g : ℕ → ℝ) (a b c d : ℝ) :
    cov S (fun n => a * f n + c) (fun n => b * g n + d) = a * b * cov S f g := by
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simp [cov_empty]
  · have hN : (S.card : ℝ) ≠ 0 := by
      have : 0 < S.card := Finset.card_pos.mpr hS
      positivity
    have h1 : ∑ n ∈ S, ((a * f n + c) * (b * g n + d))
        = a * b * (∑ n ∈ S, f n * g n) + a * d * (∑ n ∈ S, f n)
          + c * b * (∑ n ∈ S, g n) + c * d * S.card := by
      rw [Finset.sum_congr rfl (fun n _ => by ring :
        ∀ n ∈ S, (a * f n + c) * (b * g n + d)
          = a * b * (f n * g n) + a * d * f n + c * b * g n + c * d)]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
      ring
    have h2 : ∑ n ∈ S, (a * f n + c) = a * (∑ n ∈ S, f n) + c * S.card := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
      ring
    have h3 : ∑ n ∈ S, (b * g n + d) = b * (∑ n ∈ S, g n) + d * S.card := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
      ring
    simp only [cov, mean, h1, h2, h3]
    field_simp
    ring

/-- **Goldbach Covariance Transfer.**
For any finite family `S` of integers, any lag `k`, and any affine renormalisation
`r ↦ a * r + c`, `r ↦ b * r + d` of the Goldbach representation counts, the empirical
covariance of the renormalised counts of `n` and of `n + k` equals `a * b` times the
covariance of the raw counts. In particular, the vanishing (and, for `a * b > 0`, the sign)
of the Goldbach count covariance is invariant under affine renormalisation. -/
