import Brockian.GoldbachComb

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

namespace Brockian.GoldbachComb

/-- The set of ordered Goldbach pairs of `n`: pairs of primes `(p, q)` with `p + q = n`. -/

theorem gCov_fst_snd (n : ℕ) :
    gCov n (fun pq => (pq.1 : ℝ)) (fun pq => (pq.2 : ℝ))
      = - gVar n (fun pq => (pq.1 : ℝ)) := by
  classical
  set k : ℝ := ((goldbachPairs n).card : ℝ) with hk
  set s : ℝ := ∑ pq ∈ goldbachPairs n, ((pq.1 : ℕ) : ℝ) with hs
  set q : ℝ := ∑ pq ∈ goldbachPairs n, ((pq.1 : ℕ) : ℝ) ^ 2 with hq
  have hprod : ∑ pq ∈ goldbachPairs n, ((pq.1 : ℕ) : ℝ) * ((pq.2 : ℕ) : ℝ)
      = (n : ℝ) * s - q := by
    rw [hs, hq, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun pq hpq => ?_)
    rw [fst_cast_le hpq]; ring
  have hsnd : ∑ pq ∈ goldbachPairs n, ((pq.2 : ℕ) : ℝ) = (n : ℝ) * k - s := by
    rw [Finset.sum_congr rfl (fun pq hpq => fst_cast_le hpq), Finset.sum_sub_distrib,
      Finset.sum_const, nsmul_eq_mul, ← hs, ← hk]
    ring
  simp only [gVar, gCov, gMean]
  rw [hprod, hsnd]
  simp only [← hs, ← hk]
  rcases eq_or_ne k 0 with h0 | h0
  · rw [h0]; simp
  · field_simp
    ring

end AntiCorrelation

/-- **Goldbach Covariance Transfer.**

For every `n` and all real-valued statistics `f`, `g` of a prime summand, the empirical
covariance structure on the set of ordered Goldbach representations `p + q = n` satisfies:

1. *(swap transfer)* the covariance is invariant under exchanging the roles of the two
   summands;
2. *(reflection transfer)* a covariance between the two coordinates transfers to a
   covariance of statistics of the single coordinate `p`, via `q = n - p`;
3. *(variance transfer)* the two summands carry the same empirical variance;
4. *(perfect anti-correlation)* the covariance of `p` with `q` is minus the variance of `p`.
-/
