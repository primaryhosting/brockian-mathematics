import Mathlib
import Topology.Brouwer

namespace MS.Topology

/-- **Brouwer's fixed point theorem** for the closed unit ball of `EuclideanSpace ℝ (Fin n)`. -/

lemma exists_equiv_id_add_smul (A : E →L[ℝ] E) {t : ℝ} (h : ‖t • A‖ < 1) :
    ∃ e : E ≃L[ℝ] E, (e : E →L[ℝ] E) = ContinuousLinearMap.id ℝ E + t • A := by
  have hinj : Function.Injective
      ((ContinuousLinearMap.id ℝ E + t • A : E →L[ℝ] E) : E →ₗ[ℝ] E) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    by_contra hy0
    have h1 : y + (t • A) y = 0 := by simpa using hy
    have h3 : (t • A) y = -y := by linear_combination (norm := module) h1
    have h2 : ‖y‖ ≤ ‖t • A‖ * ‖y‖ := by
      calc ‖y‖ = ‖(t • A) y‖ := by rw [h3, norm_neg]
      _ ≤ ‖t • A‖ * ‖y‖ := (t • A).le_opNorm y
    have := norm_pos_iff.mpr hy0
    nlinarith
  have hbij : Function.Bijective
      ((ContinuousLinearMap.id ℝ E + t • A : E →L[ℝ] E) : E →ₗ[ℝ] E) :=
    ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩
  refine ⟨(LinearEquiv.ofBijective _ hbij).toContinuousLinearEquiv, ?_⟩
  ext y
  rfl

