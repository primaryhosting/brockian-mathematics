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


open scoped BigOperators

namespace Brockian
namespace GoldbachComb

/-- The set of Goldbach summands of `n`: primes `p ≤ n` such that `n - p` is also prime.
Thus `p ∈ goldbachSet n` exactly when `p + (n - p) = n` is a Goldbach decomposition of `n`. -/

lemma cov_const_sub (s : Finset ℕ) (c : ℝ) (f h : ℕ → ℝ) :
    cov s (fun p => c - f p) h = - cov s f h := by
  rcases Nat.eq_zero_or_pos s.card with hc | hc
  · have hs : s = ∅ := Finset.card_eq_zero.mp hc
    simp [cov, mean, hs]
  · have hcard : (s.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hc.ne'
    have h1 : mean s (fun p => (c - f p) * h p)
        = c * mean s h - mean s (fun p => f p * h p) := by
      unfold mean
      rw [mul_div_assoc', div_sub_div_same]
      congr 1
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun p _ => by ring
    have h2 : mean s (fun p => c - f p) = c - mean s f := by
      unfold mean
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
      field_simp
    unfold cov
    rw [h1, h2]
    ring

/--
**Goldbach anticovariance.**

A consequence of the covariance transfer: the covariance of the summand `p` with any statistic
of its Goldbach partner `n - p` is the negative of the covariance of `p` with that statistic
of `p` itself.
-/
