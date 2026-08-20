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
# Scalar integrals used in the integral representations
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace QI


theorem povm_sq_le (hE : IsPOVM E) (c : Y → ℝ) :
    ((∑ y, ((c y ^ 2 : ℝ) : ℂ) • E y) -
      (∑ y, ((c y : ℝ) : ℂ) • E y) * (∑ y, ((c y : ℝ) : ℂ) • E y)).PosSemidef := by
  classical
  set A : Mat n := ∑ y, ((c y : ℝ) : ℂ) • E y with hAdef
  have hherm : ∀ y, (E y)ᴴ = E y := fun y => (hE.posSemidef y).isHermitian
  have hAherm : Aᴴ = A := by
    rw [hAdef]
    simp [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, hherm]
  have expand : ∀ y : Y, (((c y : ℝ) : ℂ) • (1 : Mat n) - A) * E y * (((c y : ℝ) : ℂ) • 1 - A)
      = ((c y ^ 2 : ℝ) : ℂ) • E y - ((c y : ℝ) : ℂ) • (E y * A) - ((c y : ℝ) : ℂ) • (A * E y)
        + A * E y * A := by
    intro y
    simp only [sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one, smul_smul]
    push_cast [pow_two]
    abel
  have h1 : ∑ y, ((c y : ℝ) : ℂ) • (E y * A) = A * A := by
    conv_rhs => rw [hAdef]
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun y _ => (smul_mul_assoc _ _ _).symm
  have h2 : ∑ y, ((c y : ℝ) : ℂ) • (A * E y) = A * A := by
    conv_rhs => rw [hAdef]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => (mul_smul_comm _ _ _).symm
  have h3 : ∑ y, A * E y * A = A * A := by
    rw [show (∑ y, A * E y * A) = (∑ y, A * E y) * A by rw [Finset.sum_mul],
      ← Finset.mul_sum, hE.sum_eq_one, mul_one]
  have key : (∑ y, ((c y ^ 2 : ℝ) : ℂ) • E y) - A * A
      = ∑ y, (((c y : ℝ) : ℂ) • (1 : Mat n) - A)ᴴ * E y * (((c y : ℝ) : ℂ) • 1 - A) := by
    have hstar : ∀ y : Y, (((c y : ℝ) : ℂ) • (1 : Mat n) - A)ᴴ = ((c y : ℝ) : ℂ) • 1 - A := by
      intro y
      simp [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, hAherm]
    simp only [hstar, expand]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib, h1, h2, h3]
    abel
  rw [key]
  refine posSemidef_sum _ _ fun y _ => ?_
  exact (hE.posSemidef y).conjTranspose_mul_mul_same _

/-- Trace against a real linear combination of the POVM elements. -/
