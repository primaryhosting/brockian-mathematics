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
open scoped TensorProduct

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace QC

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- In a complex inner product space of rank at least `2` there is a pair of
orthonormal vectors. -/
theorem exists_orthonormal_pair (h : 2 ≤ Module.rank ℂ H) :
    ∃ a b : H, ‖a‖ = 1 ∧ ‖b‖ = 1 ∧ inner ℂ a b = (0 : ℂ) := by
  obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_rank (R := ℂ) (M := H) (n := 2) (by
    exact_mod_cast h)
  have ho : Orthonormal ℂ (InnerProductSpace.gramSchmidtNormed ℂ f) :=
    InnerProductSpace.gramSchmidtNormed_orthonormal hf
  exact ⟨InnerProductSpace.gramSchmidtNormed ℂ f 0, InnerProductSpace.gramSchmidtNormed ℂ f 1,
    ho.1 0, ho.1 1, ho.2 (by decide)⟩

/-- The superposition `(a + b)/√2` of two orthonormal vectors is a unit vector. -/
theorem norm_superposition {a b : H} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hab : inner ℂ a b = (0 : ℂ)) :
    ‖((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • (a + b)‖ = 1 := by
  have h2 : ‖a + b‖ ^ 2 = 2 := by
    rw [@norm_add_sq ℂ, ha, hb, hab]
    norm_num
  have hnn : (0:ℝ) ≤ ‖a + b‖ := norm_nonneg _
  have hval : ‖a + b‖ = Real.sqrt 2 := by
    rw [← h2, Real.sqrt_sq hnn]
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  rw [norm_smul, hval]
  simp only [norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg 2)]
  exact inv_mul_cancel₀ hs

/-- The inner product of `a` with the superposition `(a+b)/√2` is `1/√2`. -/
theorem inner_superposition {a b : H} (ha : ‖a‖ = 1) (hab : inner ℂ a b = (0 : ℂ)) :
    inner ℂ a (((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • (a + b)) = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ := by
  rw [inner_smul_right, inner_add_right, hab, inner_self_eq_norm_sq_to_K, ha]
  norm_num

/-- **No-cloning theorem.** If `H` is a complex inner product space of rank at least `2`,
then for no vector `e : H` is there a unitary `U` on `H ⊗ H` with
`U (ψ ⊗ e) = ψ ⊗ ψ` for every state (unit vector) `ψ`. -/
theorem no_cloning (h : 2 ≤ Module.rank ℂ H) (e : H) :
    ¬ ∃ U : (H ⊗[ℂ] H) ≃ₗᵢ[ℂ] (H ⊗[ℂ] H),
      ∀ ψ : H, ‖ψ‖ = 1 → U (ψ ⊗ₜ[ℂ] e) = ψ ⊗ₜ[ℂ] ψ := by
  rintro ⟨U, hU⟩
  obtain ⟨a, b, ha, hb, hab⟩ := exists_orthonormal_pair h
  set c : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ with hc
  set p : H := c • (a + b) with hp
  have hpnorm : ‖p‖ = 1 := norm_superposition ha hb hab
  have hinner : inner ℂ a p = c := inner_superposition ha hab
  -- the ancilla `e` must be a unit vector
  have hlen : ‖e‖ = 1 := by
    have h1 : ‖U (a ⊗ₜ[ℂ] e)‖ = ‖a ⊗ₜ[ℂ] e‖ := U.norm_map _
    rw [hU a ha] at h1
    simpa [ha] using h1.symm
  have hee : inner ℂ e e = (1 : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K, hlen]; norm_num
  -- unitarity preserves inner products
  have key : inner ℂ (U (a ⊗ₜ[ℂ] e)) (U (p ⊗ₜ[ℂ] e)) = inner ℂ (a ⊗ₜ[ℂ] e) (p ⊗ₜ[ℂ] e) :=
    U.inner_map_map _ _
  rw [hU a ha, hU p hpnorm, TensorProduct.inner_tmul, TensorProduct.inner_tmul, hinner, hee] at key
  -- so `c * c = c`, i.e. `c = 1`, contradicting `c = 1/√2`
  have hs2 : (Real.sqrt 2 : ℝ) ≠ 0 := by positivity
  have hcne : c ≠ 0 := by
    rw [hc]
    exact inv_ne_zero (by exact_mod_cast hs2)
  have hc1 : c = 1 := mul_left_cancel₀ hcne (by rw [key])
  have hroot : (Real.sqrt 2 : ℝ) = 1 := by
    have : ((Real.sqrt 2 : ℝ) : ℂ) = 1 := inv_eq_one.mp (by rw [← hc]; exact hc1)
    exact_mod_cast this
  rw [Real.sqrt_eq_one] at hroot
  norm_num at hroot

/-- The qubit case: no unitary on `ℂ² ⊗ ℂ²` clones all qubit states.  This instance of
`QC.no_cloning` also shows the rank hypothesis there is satisfiable. -/
theorem no_cloning_qubit (e : EuclideanSpace ℂ (Fin 2)) :
    ¬ ∃ U : (EuclideanSpace ℂ (Fin 2) ⊗[ℂ] EuclideanSpace ℂ (Fin 2))
        ≃ₗᵢ[ℂ] (EuclideanSpace ℂ (Fin 2) ⊗[ℂ] EuclideanSpace ℂ (Fin 2)),
      ∀ ψ : EuclideanSpace ℂ (Fin 2), ‖ψ‖ = 1 → U (ψ ⊗ₜ[ℂ] e) = ψ ⊗ₜ[ℂ] ψ := by
  refine no_cloning ?_ e
  have hf : Module.finrank ℂ (EuclideanSpace ℂ (Fin 2)) = 2 := by simp
  rw [← Module.finrank_eq_rank, hf]
  norm_num

end QC

