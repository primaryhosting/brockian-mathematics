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

/-- **Key lemma.** If a unitary `U` on `H ⊗ H` clones every unit vector against the fixed
unit "blank" state `e₀`, i.e. `U (x ⊗ e₀) = x ⊗ x`, then the inner product of any two unit
vectors is idempotent: `⟪x, y⟫ * ⟪x, y⟫ = ⟪x, y⟫`.

Indeed, unitarity gives `⟪x, y⟫ = ⟪x ⊗ e₀, y ⊗ e₀⟫ = ⟪x ⊗ x, y ⊗ y⟫ = ⟪x, y⟫²`. -/
lemma inner_mul_self_eq_inner_of_clones
    (e0 : H) (he0 : ‖e0‖ = 1)
    (U : (H ⊗[ℂ] H) ≃ₗᵢ[ℂ] (H ⊗[ℂ] H))
    (hU : ∀ x : H, ‖x‖ = 1 → U (x ⊗ₜ[ℂ] e0) = x ⊗ₜ[ℂ] x)
    (x y : H) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    (inner ℂ x y) * (inner ℂ x y) = inner ℂ x y := by
  have h := U.inner_map_map (x ⊗ₜ[ℂ] e0) (y ⊗ₜ[ℂ] e0)
  rw [hU x hx, hU y hy] at h
  simp [TensorProduct.inner_tmul, inner_self_eq_norm_sq_to_K, he0] at h
  simpa using h

/-- In a complex inner product space of rank at least two there is an orthonormal pair. -/
lemma exists_orthonormal_pair (h2 : 1 < Module.rank ℂ H) :
    ∃ u v : H, ‖u‖ = 1 ∧ ‖v‖ = 1 ∧ inner ℂ u v = 0 := by
  have h : ¬ (Module.rank ℂ H ≤ 1) := not_le.2 h2
  rw [rank_le_one_iff] at h
  push_neg at h
  obtain ⟨b, hb⟩ := h 0
  obtain ⟨a, ha⟩ := h b
  have hb0 : b ≠ 0 := by simpa using (hb 0).symm
  set u : H := (‖b‖ : ℂ)⁻¹ • b with hu_def
  have hnb : (‖b‖ : ℝ) ≠ 0 := by simpa using hb0
  have hu : ‖u‖ = 1 := by
    rw [hu_def, norm_smul]
    simp [hnb]
  have huu : (inner ℂ u u : ℂ) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hu]; norm_num
  set w : H := a - (inner ℂ u a : ℂ) • u with hw_def
  have hw0 : w ≠ 0 := by
    intro hzero
    have hau : a = (inner ℂ u a : ℂ) • u := by
      rw [hw_def] at hzero; linear_combination (norm := module) hzero
    refine ha ((inner ℂ u a : ℂ) * (‖b‖ : ℂ)⁻¹) ?_
    rw [mul_smul]
    exact hau.symm
  have hnw : (‖w‖ : ℝ) ≠ 0 := by simpa using hw0
  have hinner : (inner ℂ u w : ℂ) = 0 := by
    rw [hw_def, inner_sub_right, inner_smul_right, huu, mul_one, sub_self]
  refine ⟨u, (‖w‖ : ℂ)⁻¹ • w, hu, ?_, ?_⟩
  · rw [norm_smul]; simp [hnw]
  · rw [inner_smul_right, hinner, mul_zero]

/-- **No-cloning theorem.** On a complex inner product space `H` of dimension at least two,
there is no unitary `U` on `H ⊗ H` with `U (x ⊗ e₀) = x ⊗ x` for every unit vector `x`,
where `e₀` is any fixed unit "blank" state. -/
theorem no_cloning (h2 : 1 < Module.rank ℂ H) (e0 : H) (he0 : ‖e0‖ = 1) :
    ¬ ∃ U : (H ⊗[ℂ] H) ≃ₗᵢ[ℂ] (H ⊗[ℂ] H),
        ∀ x : H, ‖x‖ = 1 → U (x ⊗ₜ[ℂ] e0) = x ⊗ₜ[ℂ] x := by
  rintro ⟨U, hU⟩
  obtain ⟨u, v, hu, hv, huv⟩ := exists_orthonormal_pair h2
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hs2)
  have hnorm : ‖u + v‖ = Real.sqrt 2 := by
    have hs := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero u v huv
    rw [hu, hv] at hs
    have hsq : ‖u + v‖ ^ 2 = 2 := by rw [sq, hs]; norm_num
    rw [← hsq, Real.sqrt_sq (norm_nonneg _)]
  -- the state `y = (u + v)/√2` has overlap `1/√2` with `u`
  set y : H := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • (u + v) with hy_def
  have hy : ‖y‖ = 1 := by
    rw [hy_def, norm_smul, hnorm]
    simp [abs_of_pos hs2]
  have huu : (inner ℂ u u : ℂ) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hu]; norm_num
  have hiy : (inner ℂ u y : ℂ) = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ := by
    rw [hy_def, inner_smul_right, inner_add_right, huu, huv, add_zero, mul_one]
  have hk := inner_mul_self_eq_inner_of_clones e0 he0 U hU u y hu hy
  rw [hiy] at hk
  field_simp at hk
  have hr : Real.sqrt 2 = 1 := by exact_mod_cast hk.symm
  have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  rw [hr] at hsq
  norm_num at hsq

end QC

#print axioms QC.no_cloning

