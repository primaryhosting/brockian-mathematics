import Mathlib
/-!
# Euler Pentagonal
Category: Pure Mathematics
Target: Math.euler_pentagonal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Math

/-- The smallest element of a finite set of naturals (junk value `0` if empty). -/

lemma prod_one_sub_X_pow_eq (N : ℕ) :
    (∏ i ∈ Finset.Icc 1 N, (1 - (PowerSeries.X : PowerSeries ℤ) ^ i))
      = ∑ t ∈ (Finset.Icc 1 N).powerset,
          PowerSeries.C ((-1 : ℤ) ^ t.card) * PowerSeries.X ^ (∑ i ∈ t, i) := by
  have h0 : (∏ i ∈ Finset.Icc 1 N, (1 - (PowerSeries.X : PowerSeries ℤ) ^ i))
      = ∏ i ∈ Finset.Icc 1 N, ((-((PowerSeries.X : PowerSeries ℤ) ^ i)) + 1) :=
    Finset.prod_congr rfl (fun i _ => by ring)
  rw [h0, Finset.prod_add]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [Finset.prod_const_one, mul_one, Finset.prod_neg, Finset.prod_pow_eq_pow_sum,
    map_pow, map_neg, map_one]

/-- **Euler's pentagonal number theorem, generating function form.**

For `n ≤ N`, the coefficient of `X ^ n` in the finite product `∏_{i = 1}^{N} (1 - X ^ i)`
(which agrees with the coefficient in the infinite product `∏_{i ≥ 1} (1 - X ^ i)`, the
reciprocal of the partition generating function) is `(-1) ^ k` if `n` is the generalized
pentagonal number `k (3k - 1) / 2` for some `k : ℤ`, and `0` otherwise. -/
