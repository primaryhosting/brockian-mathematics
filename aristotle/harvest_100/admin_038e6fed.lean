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
-- (The header above uses a plain block comment rather than a module docstring `/-!`,
-- since Lean 4 requires `import` to precede any module docstring.)

import Mathlib

/-!
# Mobius Root Sum 9
Category: Pure Mathematics
Target: Math.mobius_root_sum_9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset Complex

namespace Math

/-- A fixed primitive 9-th root of unity in `ℂ`. -/
noncomputable def zeta9 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 9)

theorem isPrimitiveRoot_zeta9 : IsPrimitiveRoot zeta9 9 :=
  Complex.isPrimitiveRoot_exp 9 (by norm_num)

/-- The primitive 9-th roots of unity are exactly the powers `ζ ^ i` with `i` coprime to `9`. -/
theorem primitiveRoots_nine_eq_image :
    primitiveRoots 9 ℂ =
      ((range 9).filter fun i => Nat.Coprime i 9).image fun i => zeta9 ^ i := by
  have hζ := isPrimitiveRoot_zeta9
  ext x
  simp only [mem_image, mem_filter, mem_range, mem_primitiveRoots (by norm_num : 0 < 9)]
  constructor
  · intro hx
    rw [hζ.isPrimitiveRoot_iff] at hx
    obtain ⟨i, hin, hi, H⟩ := hx
    exact ⟨i, ⟨hin, hi⟩, H⟩
  · rintro ⟨i, ⟨-, hi⟩, rfl⟩
    exact hζ.pow_of_coprime i hi

/-- The sum of the primitive 9-th roots of unity equals `μ 9`. -/
theorem mobius_root_sum_9 :
    ∑ z ∈ primitiveRoots 9 ℂ, z = (ArithmeticFunction.moebius 9 : ℂ) := by
  have hζ := isPrimitiveRoot_zeta9
  -- the full geometric sum over all ninth roots vanishes
  have h9 : ∑ i ∈ range 9, zeta9 ^ i = 0 := hζ.geom_sum_eq_zero (by norm_num)
  -- the sum over the cube roots of unity vanishes
  have hcube : IsPrimitiveRoot (zeta9 ^ 3) 3 := hζ.pow (by norm_num) (by norm_num)
  have h3 : ∑ i ∈ range 3, (zeta9 ^ 3) ^ i = 0 := hcube.geom_sum_eq_zero (by norm_num)
  have hsum : ∑ z ∈ primitiveRoots 9 ℂ, z = 0 := by
    rw [primitiveRoots_nine_eq_image, Finset.sum_image]
    · have h1 : ∑ i ∈ (range 9).filter (fun i => Nat.Coprime i 9), zeta9 ^ i
          = (∑ i ∈ range 9, zeta9 ^ i) - ∑ i ∈ range 3, (zeta9 ^ 3) ^ i := by
        simp only [Finset.sum_filter, Finset.sum_range_succ, Finset.sum_range_zero,
          ← pow_mul]
        norm_num [Nat.Coprime]
        ring
      rw [h1, h9, h3, sub_zero]
    · intro i hi j hj hij
      simp only [Finset.mem_coe, mem_filter, mem_range] at hi hj
      exact hζ.pow_inj hi.1 hj.1 hij
  rw [hsum]
  have hns : ¬ Squarefree 9 := by
    intro h
    have h3 := h 3 (by norm_num)
    rw [Nat.isUnit_iff] at h3
    norm_num at h3
  have : ArithmeticFunction.moebius 9 = 0 :=
    ArithmeticFunction.moebius_eq_zero_of_not_squarefree hns
  rw [this]
  norm_num

end Math

