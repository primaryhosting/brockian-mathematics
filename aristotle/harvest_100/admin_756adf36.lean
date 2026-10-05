/-
# No Cloning
Category: Quantum Computing
Target: QC.no_cloning
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# No Cloning
Category: Quantum Computing
Target: QC.no_cloning
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

/-- A single qubit: the two-dimensional complex Hilbert space `ℂ²`. -/
abbrev Qubit : Type := EuclideanSpace ℂ (Fin 2)

/-- The tensor square `Qubit ⊗ Qubit`, realized as `ℂ^(Fin 2 × Fin 2)`. -/
abbrev Pair : Type := EuclideanSpace ℂ (Fin 2 × Fin 2)

/-- The tensor product `|ψ⟩ ⊗ |φ⟩` of two qubit states. -/
noncomputable def tens (ψ φ : Qubit) : Pair :=
  WithLp.toLp 2 (fun i => ψ i.1 * φ i.2)

@[simp] lemma tens_apply (ψ φ : Qubit) (i : Fin 2 × Fin 2) :
    tens ψ φ i = ψ i.1 * φ i.2 := rfl

/-- The blank state `|0⟩` into which the unknown state is to be copied. -/
noncomputable def zeroState : Qubit := EuclideanSpace.single 0 1

/-- **No-cloning theorem.** There is no unitary `U` on `H ⊗ H` (here `H = ℂ²`) with
`U (|ψ⟩ ⊗ |0⟩) = |ψ⟩ ⊗ |ψ⟩` for every state (unit vector) `|ψ⟩`. -/
theorem no_cloning :
    ¬ ∃ U : Pair ≃ₗᵢ[ℂ] Pair, ∀ ψ : Qubit, ‖ψ‖ = 1 → U (tens ψ zeroState) = tens ψ ψ := by
  rintro ⟨U, hU⟩
  set a : Qubit := EuclideanSpace.single 0 1 with ha
  set b : Qubit := EuclideanSpace.single 1 1 with hb
  set c : ℂ := (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) with hc
  set s : Qubit := c • (a + b) with hs
  have hcsq : c * c = 1 / 2 := by
    have h2 : ((Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ : ℝ) = 1 / 2 := by
      rw [← mul_inv, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
      norm_num
    rw [hc, ← Complex.ofReal_mul, h2]
    norm_num
  have hna : ‖a‖ = 1 := by simp [ha]
  have hnb : ‖b‖ = 1 := by simp [hb]
  have hs0 : s 0 = c := by simp [hs, ha, hb, EuclideanSpace.single_apply]
  have hs1 : s 1 = c := by simp [hs, ha, hb, EuclideanSpace.single_apply]
  have hns : ‖s‖ = 1 := by
    rw [EuclideanSpace.norm_eq]
    have h0 : ‖(s.ofLp 0 : ℂ)‖ ^ 2 = 1 / 2 := by
      have : (s.ofLp 0 : ℂ) = c := hs0
      rw [this, hc]
      rw [Complex.norm_real]
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      rw [← Real.sqrt_inv]
      rw [Real.sq_sqrt (by norm_num)]
      norm_num
    have h1 : ‖(s.ofLp 1 : ℂ)‖ ^ 2 = 1 / 2 := by
      have : (s.ofLp 1 : ℂ) = c := hs1
      rw [this, hc]
      rw [Complex.norm_real]
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      rw [← Real.sqrt_inv]
      rw [Real.sq_sqrt (by norm_num)]
      norm_num
    rw [Fin.sum_univ_two, h0, h1]
    norm_num
  -- linearity of the tensor product in the first factor
  have hsplit : tens s zeroState = c • (tens a zeroState + tens b zeroState) := by
    ext i
    simp [hs, mul_add, mul_comm, mul_left_comm]
  have key : U (tens s zeroState) = c • (tens a a + tens b b) := by
    rw [hsplit]
    rw [map_smul, map_add, hU a hna, hU b hnb]
  have hfin : tens s s = c • (tens a a + tens b b) := by
    rw [← key, hU s hns]
  -- evaluate at the coordinate `(0,1)`
  have := congrArg (fun v : Pair => v (0, 1)) hfin
  simp only [tens_apply] at this
  rw [hs0, hs1] at this
  have hzero : (c • (tens a a + tens b b) : Pair) (0, 1) = 0 := by
    simp [ha, hb, EuclideanSpace.single_apply]
  rw [hzero] at this
  rw [hcsq] at this
  norm_num at this

end QC

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

