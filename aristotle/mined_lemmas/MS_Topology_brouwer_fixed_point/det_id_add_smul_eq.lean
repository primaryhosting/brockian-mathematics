import Mathlib
import Topology.Brouwer

namespace MS.Topology

/-- **Brouwer's fixed point theorem** for the closed unit ball of `EuclideanSpace ℝ (Fin n)`. -/

lemma det_id_add_smul_eq (b : Basis ι ℝ E) (A : E →L[ℝ] E) (t : ℝ) :
    (ContinuousLinearMap.id ℝ E + t • A).det =
      ∑ p ∈ (Finset.univ : Finset (Equiv.Perm ι × Finset ι)),
        t ^ (Finset.univ \ p.2).card * coef b p.1 p.2 A := by
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix b]
  have hM : LinearMap.toMatrix b b ((ContinuousLinearMap.id ℝ E + t • A : E →L[ℝ] E) : E →ₗ[ℝ] E)
      = 1 + t • LinearMap.toMatrix b b (A : E →ₗ[ℝ] E) := by
    simp only [ContinuousLinearMap.coe_add, ContinuousLinearMap.coe_smul,
      ContinuousLinearMap.coe_id, map_add, map_smul, LinearMap.toMatrix_id]
  rw [hM, Matrix.det_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have h1 : ∀ i : ι, ((1 : Matrix ι ι ℝ) + t • LinearMap.toMatrix b b (A : E →ₗ[ℝ] E)) (σ i) i
      = (if σ i = i then (1 : ℝ) else 0)
          + t * LinearMap.toMatrix b b (A : E →ₗ[ℝ] E) (σ i) i := by
    intro i; simp [Matrix.one_apply]
  simp only [h1]
  rw [Finset.prod_add, Finset.smul_sum, ← Finset.powerset_univ]
  refine Finset.sum_congr rfl fun S _ => ?_
  simp [coef, Finset.prod_mul_distrib, Units.smul_def]
  ring

end Det

/-! ### Positivity and nonvanishing of `det (id + t A)` -/

section DetPos

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

