import Mathlib

/-!
# Mobius Root Sum 8
Category: Pure Mathematics
Target: Math.mobius_root_sum_8
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

/-- If `ζ` is a primitive `8`-th root of unity in `ℂ`, then `ζ ^ 4 = -1`. -/
theorem pow_four_eq_neg_one_of_isPrimitiveRoot_eight {ζ : ℂ} (h : IsPrimitiveRoot ζ 8) :
    ζ ^ 4 = -1 := by
  have hsq : (ζ ^ 4) ^ 2 = 1 := by
    rw [← pow_mul]
    exact h.pow_eq_one
  have h4 : ζ ^ 4 ≠ 1 := h.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
  have hfac : (ζ ^ 4 - 1) * (ζ ^ 4 + 1) = 0 := by linear_combination hsq
  rcases mul_eq_zero.mp hfac with h1 | h2
  · exact absurd (by linear_combination h1) h4
  · linear_combination h2

/-- If `ζ` is a primitive `8`-th root of unity in `ℂ`, then so is `-ζ`. -/
theorem isPrimitiveRoot_neg_of_isPrimitiveRoot_eight {ζ : ℂ} (h : IsPrimitiveRoot ζ 8) :
    IsPrimitiveRoot (-ζ) 8 := by
  have h4 : ζ ^ 4 = -1 := pow_four_eq_neg_one_of_isPrimitiveRoot_eight h
  have : -ζ = ζ ^ 5 := by
    have : ζ ^ 5 = ζ ^ 4 * ζ := by ring
    rw [this, h4]; ring
  rw [this]
  exact h.pow_of_coprime 5 (by norm_num)

/-- The sum of the primitive `8`-th roots of unity (in `ℂ`) equals `μ 8`. -/
theorem mobius_root_sum_8 :
    ∑ z ∈ primitiveRoots 8 ℂ, z = (ArithmeticFunction.moebius 8 : ℂ) := by
  have hmu : ArithmeticFunction.moebius 8 = 0 := by
    apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
    intro hsq
    simpa using hsq 2 (by norm_num)
  rw [hmu]
  push_cast
  refine Finset.sum_involution (fun a _ => -a) ?_ ?_ ?_ ?_
  · intro a _
    ring
  · intro a ha _
    have h : IsPrimitiveRoot a 8 := (mem_primitiveRoots (by norm_num)).mp ha
    have ha0 : a ≠ 0 := h.ne_zero (by norm_num)
    intro hcon
    apply ha0
    have : (2 : ℂ) * a = 0 := by linear_combination -hcon
    simpa using this
  · intro a ha
    have h : IsPrimitiveRoot a 8 := (mem_primitiveRoots (by norm_num)).mp ha
    exact (mem_primitiveRoots (by norm_num)).mpr
      (isPrimitiveRoot_neg_of_isPrimitiveRoot_eight h)
  · intro a _
    simp

end Math

