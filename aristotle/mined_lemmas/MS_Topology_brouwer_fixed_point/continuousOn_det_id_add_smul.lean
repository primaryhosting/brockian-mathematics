import Mathlib
import Topology.Brouwer

namespace MS.Topology

/-- **Brouwer's fixed point theorem** for the closed unit ball of `EuclideanSpace ℝ (Fin n)`. -/

lemma continuousOn_det_id_add_smul {s : Set E} {A : E → E →L[ℝ] E} (hA : ContinuousOn A s)
    (t : ℝ) : ContinuousOn (fun x => (ContinuousLinearMap.id ℝ E + t • A x).det) s := by
  simp only [fun x => det_id_add_smul_eq (Module.finBasis ℝ E) (A x) t]
  exact continuousOn_finset_sum _ fun p _ =>
    continuousOn_const.mul ((continuous_coef _ p.1 p.2).comp_continuousOn hA)

end DetPos

/-! ### The volume integral is a polynomial in `t` -/

section Poly

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

