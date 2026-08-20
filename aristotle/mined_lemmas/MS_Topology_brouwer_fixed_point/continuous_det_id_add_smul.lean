import Mathlib
import Topology.Brouwer

namespace MS.Topology

/-- **Brouwer's fixed point theorem** for the closed unit ball of `EuclideanSpace ℝ (Fin n)`. -/

lemma continuous_det_id_add_smul (A : E →L[ℝ] E) :
    Continuous fun t : ℝ => (ContinuousLinearMap.id ℝ E + t • A).det := by
  simp only [fun t : ℝ => det_id_add_smul_eq (Module.finBasis ℝ E) A t]
  exact continuous_finset_sum _ fun p _ => (continuous_pow _).mul continuous_const

