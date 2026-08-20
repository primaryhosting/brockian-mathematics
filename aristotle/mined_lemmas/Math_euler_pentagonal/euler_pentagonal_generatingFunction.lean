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

theorem euler_pentagonal_generatingFunction {n N : ℕ} (h : n ≤ N) :
    PowerSeries.coeff n (∏ i ∈ Finset.Icc 1 N, (1 - (PowerSeries.X : PowerSeries ℤ) ^ i))
      = ∑ k ∈ Finset.Icc (-(n : ℤ)) (n : ℤ),
          if (2 * n : ℤ) = k * (3 * k - 1) then (-1 : ℤ) ^ k.natAbs else 0 := by
  rw [prod_one_sub_X_pow_eq, map_sum]
  have hterm : ∀ t ∈ (Finset.Icc 1 N).powerset,
      PowerSeries.coeff n (PowerSeries.C ((-1 : ℤ) ^ t.card) * PowerSeries.X ^ (∑ i ∈ t, i))
        = if (∑ i ∈ t, i) = n then (-1 : ℤ) ^ t.card else 0 := by
    intro t _
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
    by_cases hc : (∑ i ∈ t, i) = n
    · rw [if_pos hc.symm, if_pos hc, mul_one]
    · rw [if_neg (fun hh => hc hh.symm), if_neg hc, mul_zero]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter, ← D_eq_powerset_filter h,
    euler_pentagonal]

end Math

