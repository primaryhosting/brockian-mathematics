/-
# Donsker Invariance
Category: Frontier Math
Target: Math2.donsker_invariance
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Donsker Invariance
Category: Frontier Math
Target: Math2.donsker_invariance
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Math2

/-- The linearly interpolated, rescaled random walk
`W_n(t) = (S_{⌊nt⌋} + (nt - ⌊nt⌋) X_{⌊nt⌋}) / √n`, where `S_m = X_0 + ⋯ + X_{m-1}`.
This is the classical Donsker polygonal process associated to the steps `X`. -/

lemma tendsto_integral_donskerInterp {X : ℕ → Ω → ℝ} (hmeas : ∀ i, Measurable (X i))
    (hindep : iIndepFun X P) (hlaw : ∀ i, P.map (X i) = gaussianReal 0 1)
    {t : ℝ} (ht : 0 ≤ t) (f : BoundedContinuousFunction ℝ ℝ) :
    Tendsto (fun n : ℕ ↦ ∫ ω, f (donskerInterp X n t ω) ∂P) atTop
      (𝓝 (∫ x, f x ∂(gaussianReal 0 t.toNNReal))) := by
  have h2 : ∀ n : ℕ, ∫ ω, f (donskerInterp X n t ω) ∂P
      = ∫ x, f x ∂(gaussianReal 0 (donskerVar n t)) := by
    intro n
    rw [← map_donskerInterp hmeas hindep hlaw n t,
      integral_map (measurable_donskerInterp hmeas n t).aemeasurable
        f.continuous.aestronglyMeasurable]
  simp_rw [h2]
  refine tendsto_integral_gaussianReal ?_ f
  simpa [Real.coe_toNNReal t ht] using tendsto_donskerVar ht

end Lemmas

/-- **Donsker's invariance principle**, one-dimensional time marginals of the polygonal process.

If `X 0, X 1, …` are i.i.d. standard Gaussian random variables and
`W_n(t) = (S_{⌊nt⌋} + (nt-⌊nt⌋)X_{⌊nt⌋})/√n` is the associated rescaled polygonal random walk,
then for every `t ≥ 0` the law of `W_n(t)` converges weakly to the law of `B t`, for any
Brownian motion `B`; that is, `∫ f(W_n(t)) dP → E[f(B t)]` for every bounded continuous `f`. -/
