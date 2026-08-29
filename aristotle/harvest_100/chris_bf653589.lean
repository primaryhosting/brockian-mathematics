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
# Mobius Root Sum 9
Category: Pure Mathematics
Target: Math.mobius_root_sum_9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Mobius Root Sum 9
Category: Pure Mathematics
Target: Math.mobius_root_sum_9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset Polynomial

namespace Math

/-- The sum of the primitive `9`-th roots of unity in `ℂ` equals `μ(9) = 0`.

The primitive `9`-th roots of unity are exactly the roots of the cyclotomic polynomial
`Φ₉ = 1 + X³ + X⁶`, whose next-to-leading coefficient (the coefficient of `X⁵`) vanishes;
hence the sum of its roots is `0`, which is also the value of the Möbius function at `9`
(since `9` is not squarefree). -/
theorem mobius_root_sum_9 :
    ∑ z ∈ primitiveRoots 9 ℂ, z = (ArithmeticFunction.moebius 9 : ℂ) := by
  have hc : (cyclotomic 9 ℂ) = 1 + X ^ 3 + X ^ 6 := by
    have h := cyclotomic_prime_pow_eq_geom_sum (R := ℂ) (p := 3) (n := 1) (by norm_num)
    simp [Finset.sum_range_succ] at h
    rw [h]; ring
  have hsplits : (cyclotomic 9 ℂ).Splits := IsAlgClosed.splits _
  have hmon : (cyclotomic 9 ℂ).Monic := cyclotomic.monic 9 ℂ
  have h := hsplits.nextCoeff_eq_neg_sum_roots_of_monic hmon
  have hnext : (cyclotomic 9 ℂ).nextCoeff = 0 := by
    rw [hc, nextCoeff]
    norm_num [Polynomial.natDegree_add_eq_right_of_natDegree_lt, coeff_one, coeff_X_pow]
  have hmu : (ArithmeticFunction.moebius 9 : ℂ) = 0 := by
    rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree
      (by simp [Nat.squarefree_iff_prime_squarefree]; exact ⟨3, by norm_num, by norm_num⟩)]
    norm_num
  rw [← cyclotomic.roots_to_finset_eq_primitiveRoots, hmu]
  show Multiset.sum _ = _
  have : -(cyclotomic 9 ℂ).roots.sum = 0 := by rw [← h, hnext]
  simpa using neg_eq_zero.mp this

end Math

