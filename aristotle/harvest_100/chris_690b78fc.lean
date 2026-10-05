/-
# No Cloning
Category: Quantum Computing
Target: QC.no_cloning
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped TensorProduct

namespace QC

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The superposition `(a + b)/√2` of two orthonormal vectors is again a unit vector. -/
lemma norm_superposition (a b : H) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hab : inner ℂ a b = (0 : ℂ)) :
    ‖((Real.sqrt 2 : ℝ)⁻¹ : ℂ) • (a + b)‖ = 1 := by
  have h2 : ‖a + b‖ * ‖a + b‖ = 2 := by
    rw [norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero a b hab, ha, hb]; norm_num
  have hnn : (0 : ℝ) ≤ ‖a + b‖ := norm_nonneg _
  have hab2 : ‖a + b‖ = Real.sqrt 2 := by
    rw [show (2 : ℝ) = ‖a + b‖ * ‖a + b‖ from h2.symm, Real.sqrt_mul_self hnn]
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  rw [norm_smul, hab2]
  simp [abs_of_nonneg (Real.sqrt_nonneg 2), hs]

/-- The inner product of `a` with the superposition `(a + b)/√2` is `1/√2`. -/
lemma inner_superposition (a b : H) (ha : ‖a‖ = 1) (hab : inner ℂ a b = (0 : ℂ)) :
    inner ℂ a (((Real.sqrt 2 : ℝ)⁻¹ : ℂ) • (a + b)) = ((Real.sqrt 2 : ℝ)⁻¹ : ℂ) := by
  rw [inner_smul_right, inner_add_right, hab, inner_self_eq_norm_sq_to_K, ha]
  norm_num

/--
**No-cloning theorem.**

Let `H` be a complex inner product space containing two orthonormal vectors `a`, `b`
(i.e. `H` has dimension at least `2`), and let `e0` be any unit "blank" state.
Then there is no unitary (linear isometry equivalence) `U` on `H ⊗ H` with
`U (ψ ⊗ e0) = ψ ⊗ ψ` for every state (unit vector) `ψ`.
-/
theorem no_cloning (a b : H) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hab : inner ℂ a b = (0 : ℂ))
    (e0 : H) (he0 : ‖e0‖ = 1) :
    ¬ ∃ U : H ⊗[ℂ] H ≃ₗᵢ[ℂ] H ⊗[ℂ] H,
        ∀ ψ : H, ‖ψ‖ = 1 → U (ψ ⊗ₜ[ℂ] e0) = ψ ⊗ₜ[ℂ] ψ := by
  rintro ⟨U, hU⟩
  set r : ℂ := ((Real.sqrt 2 : ℝ)⁻¹ : ℂ) with hr
  set c : H := r • (a + b) with hc
  have hcnorm : ‖c‖ = 1 := norm_superposition a b ha hb hab
  have hac : inner ℂ a c = r := inner_superposition a b ha hab
  -- unitarity: the inner product before and after applying `U` agree
  have key : inner ℂ (U (a ⊗ₜ[ℂ] e0)) (U (c ⊗ₜ[ℂ] e0)) = inner ℂ (a ⊗ₜ[ℂ] e0) (c ⊗ₜ[ℂ] e0) :=
    U.inner_map_map _ _
  rw [hU a ha, hU c hcnorm, TensorProduct.inner_tmul, TensorProduct.inner_tmul, hac,
    inner_self_eq_norm_sq_to_K, he0] at key
  -- hence `r * r = r`
  have hrr : r * r = r := by
    simpa using key
  have hrne : r ≠ 0 := by
    simp only [hr, ne_eq, Complex.ofReal_eq_zero, inv_eq_zero]
    positivity
  have hr1 : r = 1 := mul_right_cancel₀ hrne (by rw [one_mul]; exact hrr)
  -- but `1/√2 ≠ 1`
  have hsq : ((Real.sqrt 2 : ℝ) : ℂ) = 1 := by
    rw [hr] at hr1
    field_simp at hr1
    exact hr1.symm
  have h' : Real.sqrt 2 = 1 := by exact_mod_cast hsq
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [h'] at h2
  norm_num at h2

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

