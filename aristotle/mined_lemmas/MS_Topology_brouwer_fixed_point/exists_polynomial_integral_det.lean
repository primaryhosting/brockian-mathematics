import Mathlib
import Topology.Brouwer

namespace MS.Topology

/-- **Brouwer's fixed point theorem** for the closed unit ball of `EuclideanSpace ℝ (Fin n)`. -/

lemma exists_polynomial_integral_det (A : E → (E →L[ℝ] E))
    (hA : ContinuousOn A (closedBall 0 1)) :
    ∃ q : Polynomial ℝ, ∀ t : ℝ,
      q.eval t = ∫ x in ball (0 : E) 1, (ContinuousLinearMap.id ℝ E + t • A x).det
        ∂(Measure.addHaar : Measure E) := by
  classical
  set μ : Measure E := Measure.addHaar
  set b := Module.finBasis ℝ E with hb
  have hint : ∀ (σ : Equiv.Perm (Fin (finrank ℝ E))) (S : Finset (Fin (finrank ℝ E))),
      IntegrableOn (fun x => coef b σ S (A x)) (ball (0 : E) 1) μ := by
    intro σ S
    have hc : ContinuousOn (fun x => coef b σ S (A x)) (closedBall (0 : E) 1) :=
      (continuous_coef b σ S).comp_continuousOn hA
    exact (hc.integrableOn_compact (isCompact_closedBall _ _)).mono_set ball_subset_closedBall
  refine ⟨∑ p ∈ (Finset.univ : Finset (Equiv.Perm (Fin (finrank ℝ E)) ×
      Finset (Fin (finrank ℝ E)))),
      Polynomial.C (∫ x in ball (0 : E) 1, coef b p.1 p.2 (A x) ∂μ) *
        Polynomial.X ^ ((Finset.univ \ p.2).card), fun t => ?_⟩
  rw [Polynomial.eval_finset_sum]
  have key : ∀ x, (ContinuousLinearMap.id ℝ E + t • A x).det
      = ∑ p ∈ (Finset.univ : Finset (Equiv.Perm (Fin (finrank ℝ E)) ×
          Finset (Fin (finrank ℝ E)))),
        t ^ (Finset.univ \ p.2).card * coef b p.1 p.2 (A x) := fun x => det_id_add_smul_eq b (A x) t
  simp only [key]
  rw [integral_finset_sum _ (fun p _ => (hint p.1 p.2).const_mul _)]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [integral_const_mul]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  ring

end Poly

/-! ### No `C¹` retraction of the ball onto the sphere -/

section NoRetraction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
/-- If `r` has constant norm `1` near `x`, the determinant of its derivative at `x` vanishes. -/
