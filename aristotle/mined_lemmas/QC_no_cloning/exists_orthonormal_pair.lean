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
