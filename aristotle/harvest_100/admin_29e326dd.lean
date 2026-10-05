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
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QC

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Auxiliary: from an orthonormal pair `a, b` we build the unit vector
`(3/5) • a + (4/5) • b`, whose inner product with `a` is `3/5`. -/
lemma inner_self_of_unit (a : H) (ha : ‖a‖ = 1) : inner ℂ a a = 1 := by
  rw [inner_self_eq_norm_sq_to_K, ha]
  norm_num

lemma norm_superposition (a b : H) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hab : inner ℂ a b = (0 : ℂ)) :
    ‖((3 / 5 : ℂ) • a + (4 / 5 : ℂ) • b)‖ = 1 := by
  have hba : inner ℂ b a = (0 : ℂ) := by
    rw [← inner_conj_symm, hab, map_zero]
  have haa : inner ℂ a a = (1 : ℂ) := inner_self_of_unit a ha
  have hbb : inner ℂ b b = (1 : ℂ) := inner_self_of_unit b hb
  have hself : inner ℂ ((3 / 5 : ℂ) • a + (4 / 5 : ℂ) • b)
      ((3 / 5 : ℂ) • a + (4 / 5 : ℂ) • b) = (1 : ℂ) := by
    simp only [inner_add_add_self, inner_smul_left, inner_smul_right, haa, hbb, hab, hba,
      map_div₀, Complex.conj_ofNat]
    ring
  have := norm_eq_sqrt_re_inner (𝕜 := ℂ) ((3 / 5 : ℂ) • a + (4 / 5 : ℂ) • b)
  rw [this, hself]
  norm_num

lemma inner_a_superposition (a b : H) (ha : ‖a‖ = 1)
    (hab : inner ℂ a b = (0 : ℂ)) :
    inner ℂ a ((3 / 5 : ℂ) • a + (4 / 5 : ℂ) • b) = (3 / 5 : ℂ) := by
  have haa : inner ℂ a a = (1 : ℂ) := inner_self_of_unit a ha
  rw [inner_add_right, inner_smul_right, inner_smul_right, haa, hab]
  ring

/-- **No-cloning theorem.**  There is no unitary `U` on `H ⊗ H` (a linear isometry
equivalence, i.e. an inner-product preserving linear bijection) together with a fixed
"blank" unit vector `e₀` such that `U (ψ ⊗ e₀) = ψ ⊗ ψ` for every state (unit vector) `ψ`,
as soon as `H` contains two orthogonal unit vectors (i.e. `H` has dimension at least 2). -/
theorem no_cloning
    (hH : ∃ a b : H, ‖a‖ = 1 ∧ ‖b‖ = 1 ∧ inner ℂ a b = (0 : ℂ))
    (e₀ : H) (he₀ : ‖e₀‖ = 1)
    (U : (H ⊗[ℂ] H) ≃ₗᵢ[ℂ] (H ⊗[ℂ] H))
    (hclone : ∀ ψ : H, ‖ψ‖ = 1 → U (ψ ⊗ₜ[ℂ] e₀) = ψ ⊗ₜ[ℂ] ψ) :
    False := by
  obtain ⟨a, b, ha, hb, hab⟩ := hH
  set c : H := (3 / 5 : ℂ) • a + (4 / 5 : ℂ) • b with hc
  have hcnorm : ‖c‖ = 1 := norm_superposition a b ha hb hab
  have hac : inner ℂ a c = (3 / 5 : ℂ) := inner_a_superposition a b ha hab
  have h00 : inner ℂ e₀ e₀ = (1 : ℂ) := inner_self_of_unit e₀ he₀
  have key : inner ℂ (a ⊗ₜ[ℂ] e₀) (c ⊗ₜ[ℂ] e₀)
      = inner ℂ (U (a ⊗ₜ[ℂ] e₀)) (U (c ⊗ₜ[ℂ] e₀)) := by
    rw [U.inner_map_map]
  rw [hclone a ha, hclone c hcnorm, TensorProduct.inner_tmul, TensorProduct.inner_tmul,
    hac, h00] at key
  norm_num at key

/-- The hypothesis of `QC.no_cloning` is satisfied by the qubit space
`EuclideanSpace ℂ (Fin 2)`, so the theorem is not vacuous: no unitary on a two-qubit
space can clone all qubit states. -/
theorem no_cloning_qubit
    (e₀ : EuclideanSpace ℂ (Fin 2)) (he₀ : ‖e₀‖ = 1)
    (U : (EuclideanSpace ℂ (Fin 2) ⊗[ℂ] EuclideanSpace ℂ (Fin 2))
        ≃ₗᵢ[ℂ] (EuclideanSpace ℂ (Fin 2) ⊗[ℂ] EuclideanSpace ℂ (Fin 2)))
    (hclone : ∀ ψ : EuclideanSpace ℂ (Fin 2), ‖ψ‖ = 1 → U (ψ ⊗ₜ[ℂ] e₀) = ψ ⊗ₜ[ℂ] ψ) :
    False := by
  refine no_cloning ⟨EuclideanSpace.single 0 1, EuclideanSpace.single 1 1, ?_, ?_, ?_⟩
    e₀ he₀ U hclone <;>
    simp [EuclideanSpace.norm_single, EuclideanSpace.inner_single_left]

end QC

