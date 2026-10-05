import Mathlib

/-!
# Nash Embedding
Category: Frontier Math
Target: Math2.nash_embedding
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Manifold ContDiff
open Bundle

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

namespace Math2

/-!
## Isometric embeddings of Riemannian manifolds into Euclidean space

Throughout, a *Riemannian manifold* is a smooth manifold `M` modelled on `(E, H, I)` whose
tangent bundle carries a `RiemannianBundle` structure, i.e. each tangent space
`TangentSpace I x` is endowed with an inner product (varying smoothly with `x` when one also
assumes `IsContMDiffRiemannianBundle`).  This is the Mathlib formulation of a Riemannian metric.
-/

/-- A map `f : M → ℝ^N` is an **isometric embedding** of the Riemannian manifold `M` if it is
smooth, a topological embedding, and its differential preserves inner products, i.e. the pullback
along `f` of the Euclidean metric of `ℝ^N` is the Riemannian metric of `M`. -/

noncomputable def lineMetric (a : ℝ → ℝ) (ha : ContDiff ℝ ∞ a) (hpos : ∀ x, 0 < a x) :
    ContMDiffRiemannianMetric 𝓘(ℝ, ℝ) ∞ ℝ (fun x : ℝ ↦ TangentSpace 𝓘(ℝ, ℝ) x) where
  inner x := a x • (ContinuousLinearMap.mul ℝ ℝ)
  symm x v w := by
    show a x * ((show ℝ from v) * (show ℝ from w)) = a x * ((show ℝ from w) * (show ℝ from v))
    ring
  pos x v hv := by
    show 0 < a x * ((show ℝ from v) * (show ℝ from v))
    have h1 : (0 : ℝ) < (show ℝ from v) * (show ℝ from v) := mul_self_pos.2 hv
    have h2 := hpos x
    positivity
  isVonNBounded x := by
    show Bornology.IsVonNBounded ℝ
      {v : TangentSpace 𝓘(ℝ, ℝ) x | a x * ((show ℝ from v) * (show ℝ from v)) < 1}
    have hax := hpos x
    set r : ℝ := Real.sqrt (1 / a x) with hr
    have hrpos : 0 < r := Real.sqrt_pos.2 (by positivity)
    have hr2 : r ^ 2 = 1 / a x := Real.sq_sqrt (by positivity)
    have hset : {v : TangentSpace 𝓘(ℝ, ℝ) x | a x * ((show ℝ from v) * (show ℝ from v)) < 1}
        = Metric.ball (0 : TangentSpace 𝓘(ℝ, ℝ) x) r := by
      ext v
      have hn : ‖v‖ = |(show ℝ from v)| := by
        rw [norm_tangentSpace_vectorSpace]; exact Real.norm_eq_abs _
      simp only [Set.mem_setOf_eq, Metric.mem_ball, dist_zero_right, hn]
      rw [show (show ℝ from v) * (show ℝ from v) = |(show ℝ from v)| ^ 2 by rw [sq_abs]; ring]
      constructor
      · intro h
        have h2 : |(show ℝ from v)| ^ 2 < r ^ 2 := by rw [hr2, lt_div_iff₀ hax]; linarith
        nlinarith [abs_nonneg (show ℝ from v)]
      · intro h
        have h2 : |(show ℝ from v)| ^ 2 < r ^ 2 := by nlinarith [abs_nonneg (show ℝ from v)]
        rw [hr2, lt_div_iff₀ hax] at h2; linarith
    rw [hset]
    exact NormedSpace.isVonNBounded_ball ℝ _ r
  contMDiff := by
    intro x
    rw [contMDiffAt_section]
    have key : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ →L[ℝ] ℝ →L[ℝ] ℝ) ∞
        (fun y : ℝ ↦ a y • (ContinuousLinearMap.mul ℝ ℝ)) x := by
      rw [contMDiffAt_iff_contDiffAt]
      exact (contDiff_smul_const_aux a ha (ContinuousLinearMap.mul ℝ ℝ)).contDiffAt
    convert key with y
    ext
    simp [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates,
      Trivialization.linearMapAt_apply, TangentSpace]

/-- The canonical linear isometry from `ℝ` to `ℝ¹`. -/
