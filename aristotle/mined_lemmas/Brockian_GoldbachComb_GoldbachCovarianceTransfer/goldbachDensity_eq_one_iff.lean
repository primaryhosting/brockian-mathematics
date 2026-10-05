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
# Goldbach Covariance Transfer
Category: Brockian Conjecture
Target: Brockian.GoldbachComb.GoldbachCovarianceTransfer
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators Classical

namespace Brockian.GoldbachComb

/-- `n` is Goldbach representable if it is a sum of two primes. -/

lemma goldbachDensity_eq_one_iff {S : Finset ℕ} (hS : S.Nonempty) :
    goldbachDensity S = 1 ↔ ∀ n ∈ S, Representable n := by
  have hc : (S.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr hS)
  rw [goldbachDensity, mean, div_eq_one_iff_eq hc]
  constructor
  · intro h n hn
    have hsum : ∑ m ∈ S, (1 - goldbachInd m) = 0 := by
      rw [Finset.sum_sub_distrib, h]
      simp
    have hnonneg : ∀ m ∈ S, 0 ≤ 1 - goldbachInd m := fun m _ => by
      have := goldbachInd_le_one m; linarith
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum n hn
    by_contra hcon
    rw [goldbachInd, if_neg hcon] at hzero
    norm_num at hzero
  · intro h
    rw [Finset.sum_congr rfl (fun n hn => show goldbachInd n = 1 by
      rw [goldbachInd, if_pos (h n hn)])]
    simp

/-- **Goldbach Covariance Transfer.**

For any nonempty finite set `S` of naturals:

1. (Transfer identity) The empirical covariance over `S` between the Goldbach
   representation count `r(n)` and the Goldbach indicator `1_{r(n) > 0}` factors as
   `mean(r) * (1 - density)`; i.e. the covariance carries no information beyond the
   mean count and the density of representable elements of `S`.
2. (Reduction) Consequently, whenever the mean representation count over `S` is positive,
   the covariance vanishes if and only if *every* element of `S` is a sum of two primes.
-/
