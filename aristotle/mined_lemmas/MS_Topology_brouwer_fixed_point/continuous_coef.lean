import Mathlib
import Topology.Brouwer

namespace MS.Topology

/-- **Brouwer's fixed point theorem** for the closed unit ball of `EuclideanSpace ℝ (Fin n)`. -/

lemma continuous_coef (b : Basis ι ℝ E) (σ : Equiv.Perm ι) (S : Finset ι) :
    Continuous (coef b σ S) := by
  haveI : FiniteDimensional ℝ E := Module.Finite.of_basis b
  refine Continuous.mul continuous_const (continuous_finset_prod _ fun i _ => ?_)
  simp only [LinearMap.toMatrix_apply, ContinuousLinearMap.coe_coe]
  have h1 : Continuous fun w : E => b.repr w (σ i) :=
    LinearMap.continuous_of_finiteDimensional ((Finsupp.lapply (σ i)).comp b.repr.toLinearMap)
  exact h1.comp ((ContinuousLinearMap.apply ℝ E (b i)).continuous)

/-- Expansion of `det (id + t • A)` as a polynomial expression in `t`. -/
