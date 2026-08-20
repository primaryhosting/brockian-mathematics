import Mathlib
import Topology.Brouwer

namespace MS.Topology

/-- **Brouwer's fixed point theorem** for the closed unit ball of `EuclideanSpace ℝ (Fin n)`. -/

noncomputable def coef (b : Basis ι ℝ E) (σ : Equiv.Perm ι) (S : Finset ι) (A : E →L[ℝ] E) : ℝ :=
  (Equiv.Perm.sign σ : ℝ) * (∏ i ∈ S, if σ i = i then (1 : ℝ) else 0) *
    ∏ i ∈ Finset.univ \ S, LinearMap.toMatrix b b (A : E →ₗ[ℝ] E) (σ i) i

