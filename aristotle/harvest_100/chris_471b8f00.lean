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
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QC

open scoped TensorProduct

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- **Key lemma.** If a unitary `U` on `H ⊗ H` clones every unit vector against the
"blank" unit vector `e₀`, then for any two unit vectors `u`, `v` the overlap
`⟪u, v⟫` satisfies `⟪u, v⟫ = ⟪u, v⟫ ^ 2`, since unitaries preserve inner products. -/
theorem inner_sq_eq_inner_of_cloner
    (e0 : H) (he0 : ‖e0‖ = 1)
    (U : (H ⊗[ℂ] H) ≃ₗᵢ[ℂ] (H ⊗[ℂ] H))
    (hU : ∀ u : H, ‖u‖ = 1 → U (u ⊗ₜ[ℂ] e0) = u ⊗ₜ[ℂ] u)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    inner ℂ u v = (inner ℂ u v : ℂ) ^ 2 := by
  have he0' : (inner ℂ e0 e0 : ℂ) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, he0]
    norm_num
  have h1 : (inner ℂ (U (u ⊗ₜ[ℂ] e0)) (U (v ⊗ₜ[ℂ] e0)) : ℂ)
      = inner ℂ (u ⊗ₜ[ℂ] e0) (v ⊗ₜ[ℂ] e0) := U.inner_map_map _ _
  rw [hU u hu, hU v hv, TensorProduct.inner_tmul, TensorProduct.inner_tmul, he0'] at h1
  rw [pow_two, h1, mul_one]

/-- **No-cloning theorem.** If the state space `H` contains two orthonormal vectors
`e0`, `e1` (i.e. `H` has dimension at least two), then there is no unitary `U` on
`H ⊗ H` that clones every unit vector against the blank state `e0`, i.e. satisfying
`U (u ⊗ e0) = u ⊗ u` for all unit vectors `u`. -/
theorem no_cloning
    (e0 e1 : H) (he0 : ‖e0‖ = 1) (he1 : ‖e1‖ = 1) (horth : inner ℂ e0 e1 = (0 : ℂ)) :
    ¬ ∃ U : (H ⊗[ℂ] H) ≃ₗᵢ[ℂ] (H ⊗[ℂ] H),
        ∀ u : H, ‖u‖ = 1 → U (u ⊗ₜ[ℂ] e0) = u ⊗ₜ[ℂ] u := by
  rintro ⟨U, hU⟩
  -- the superposition `v = (√2/2) • (e0 + e1)` is a unit vector
  set c : ℝ := Real.sqrt 2 / 2 with hc
  have hsqrt2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrt2pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  set v : H := (c : ℂ) • (e0 + e1) with hvdef
  have hsum : ‖e0 + e1‖ = Real.sqrt 2 := by
    have : ‖e0 + e1‖ ^ 2 = 2 := by
      rw [@norm_add_sq ℂ, horth, he0, he1]
      norm_num
    have hnn : (0:ℝ) ≤ ‖e0 + e1‖ := norm_nonneg _
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have hv : ‖v‖ = 1 := by
    rw [hvdef, norm_smul]
    rw [hsum]
    have hcn : ‖(c : ℂ)‖ = c := by
      simp [abs_of_nonneg (show (0:ℝ) ≤ c by positivity)]
    rw [hcn, hc]
    field_simp
    nlinarith
  -- the overlap of `e0` with `v`
  have hinner : (inner ℂ e0 v : ℂ) = (c : ℂ) := by
    rw [hvdef, inner_smul_right, inner_add_right, horth]
    have he0' : (inner ℂ e0 e0 : ℂ) = 1 := by
      rw [inner_self_eq_norm_sq_to_K, he0]; norm_num
    rw [he0']
    ring
  have key := inner_sq_eq_inner_of_cloner e0 he0 U hU e0 v he0 hv
  rw [hinner] at key
  -- so `c = c ^ 2` with `c = √2 / 2`, which is false
  have hcr : c = c ^ 2 := by
    have := congrArg Complex.re key
    simpa [← Complex.ofReal_pow] using this
  have : Real.sqrt 2 = 1 := by
    rw [hc] at hcr
    nlinarith
  nlinarith

/-- Non-vacuity: the hypotheses of `QC.no_cloning` are satisfiable, e.g. for a single qubit
`H = EuclideanSpace ℂ (Fin 2)` with the computational basis. Hence there is no unitary on
`H ⊗ H` cloning all qubit states. -/
theorem no_cloning_qubit :
    ¬ ∃ U : ((EuclideanSpace ℂ (Fin 2)) ⊗[ℂ] (EuclideanSpace ℂ (Fin 2)))
        ≃ₗᵢ[ℂ] ((EuclideanSpace ℂ (Fin 2)) ⊗[ℂ] (EuclideanSpace ℂ (Fin 2))),
      ∀ u : EuclideanSpace ℂ (Fin 2), ‖u‖ = 1 →
        U (u ⊗ₜ[ℂ] (EuclideanSpace.single 0 (1 : ℂ)))
          = u ⊗ₜ[ℂ] u := by
  refine no_cloning (EuclideanSpace.single 0 (1 : ℂ)) (EuclideanSpace.single 1 (1 : ℂ)) ?_ ?_ ?_
  · simp
  · simp
  · simp [EuclideanSpace.inner_single_left, EuclideanSpace.single_apply]

end QC

