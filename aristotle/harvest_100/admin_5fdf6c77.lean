import Mathlib

/-!
# Mobius Root Sum 12
Category: Pure Mathematics
Target: Math.mobius_root_sum_12
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

set_option grind.warning false

namespace Math

/-- If `z` is a primitive `12`-th root of unity in a domain, then `z ^ 6 = -1`. -/
theorem pow_six_eq_neg_one_of_isPrimitiveRoot_twelve {R : Type*} [CommRing R] [IsDomain R]
    {z : R} (hz : IsPrimitiveRoot z 12) : z ^ 6 = -1 := by
  have h1 : (z ^ 6) ^ 2 = 1 := by
    rw [← pow_mul]
    exact hz.pow_eq_one
  have h2 : z ^ 6 ≠ 1 := by
    intro h
    have hdvd : (12 : ℕ) ∣ 6 := hz.dvd_of_pow_eq_one 6 h
    omega
  have hfac : (z ^ 6 - 1) * (z ^ 6 + 1) = 0 := by linear_combination h1
  rcases mul_eq_zero.mp hfac with h | h
  · exact absurd (by linear_combination h) h2
  · linear_combination h

/-- Negation maps primitive `12`-th roots of unity to primitive `12`-th roots of unity. -/
theorem isPrimitiveRoot_neg_of_twelve {R : Type*} [CommRing R] [IsDomain R]
    {z : R} (hz : IsPrimitiveRoot z 12) : IsPrimitiveRoot (-z) 12 := by
  have h6 : z ^ 6 = -1 := pow_six_eq_neg_one_of_isPrimitiveRoot_twelve hz
  have hz7 : -z = z ^ 7 := by
    have h7 : z ^ 7 = z ^ 6 * z := by ring
    rw [h7, h6]; ring
  rw [hz7]
  exact hz.pow_of_coprime 7 (by decide)

/-- The sum of the primitive `12`-th roots of unity in `ℂ` equals `μ(12) = 0`. -/
theorem mobius_root_sum_12 :
    ∑ z ∈ primitiveRoots 12 ℂ, z = (ArithmeticFunction.moebius 12 : ℂ) := by
  have hmu : ArithmeticFunction.moebius 12 = 0 :=
    ArithmeticFunction.moebius_eq_zero_of_not_squarefree (by decide)
  rw [hmu]
  push_cast
  refine Finset.sum_involution (fun z _ => -z) ?_ ?_ ?_ ?_
  · intro z _
    ring
  · intro z _ hz0 h
    apply hz0
    linear_combination (-1/2 : ℂ) * h
  · intro z hz
    rw [mem_primitiveRoots (by norm_num)] at hz ⊢
    exact isPrimitiveRoot_neg_of_twelve hz
  · intro z _
    ring

end Math

