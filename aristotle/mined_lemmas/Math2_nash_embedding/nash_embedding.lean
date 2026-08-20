import Mathlib

/-!
# Nash Embedding
Category: Frontier Math
Target: Math2.nash_embedding
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` lines to precede every other command, including the module
-- docstring above; the requested header is otherwise reproduced verbatim.)

open scoped ContDiff
open Topology

namespace Math2

/-! ## The canonical linear isometry `ℝ →L[ℝ] ℝ¹`

We realise the target Euclidean space as `EuclideanSpace ℝ (Fin N)`.  For the construction
below only `N = 1` is needed, so we set up the canonical map `ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1)`
and record its basic properties. -/

/-- The canonical continuous linear map `ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1)`,
sending `a` to the constant family `fun _ => a`. -/

theorem nash_embedding {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hpos : ∀ x, 0 < g x) :
    ∃ (N : ℕ) (f : ℝ → EuclideanSpace ℝ (Fin N)),
      ContDiff ℝ ∞ f ∧ IsEmbedding f ∧
      ∀ x v w : ℝ, inner ℝ (fderiv ℝ f x v) (fderiv ℝ f x w) = g x * (v * w) := by
  set a : ℝ → ℝ := fun x => Real.sqrt (g x)
  have ha : ContDiff ℝ ∞ a := contDiff_sqrt_of_pos hg hpos
  have hapos : ∀ x, 0 < a x := fun x => Real.sqrt_pos.2 (hpos x)
  have hasq : ∀ x, a x * a x = g x := fun x =>
    Real.mul_self_sqrt (hpos x).le
  set F : ℝ → ℝ := fun u => ∫ t in (0 : ℝ)..u, a t
  have hF' : ∀ x, HasDerivAt F (a x) x := fun x =>
    ((ha.continuous).integral_hasStrictDerivAt 0 x).hasDerivAt
  have hFsmooth : ContDiff ℝ ∞ F := contDiff_of_hasDerivAt ha hF'
  have hFmono : StrictMono F := by
    refine strictMono_of_deriv_pos ?_
    intro x
    rw [(hF' x).deriv]
    exact hapos x
  refine ⟨1, fun x => line (F x), ?_, ?_, ?_⟩
  · exact line.contDiff.comp hFsmooth
  · exact isometry_line.isEmbedding.comp
      (isEmbedding_of_strictMono hFsmooth.continuous hFmono)
  · intro x v w
    have hfd : HasFDerivAt (fun x => line (F x))
        (line.comp (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (a x))) x :=
      line.hasFDerivAt.comp x (hF' x).hasFDerivAt
    rw [hfd.fderiv]
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply, smul_eq_mul]
    rw [inner_line]
    rw [← hasq x]
    ring

/-! ## A curved two-dimensional case: surfaces of revolution

The one-dimensional case above concerns only flat metrics.  We also treat a genuinely curved
family: the rotationally symmetric metrics `du² + h(u)² dv²` on `ℝ²` (whose Gauss curvature is
`-h''/h`, so generically nonzero).  Under the classical condition `|h'| < 1`, such a metric is
induced by the smooth map
`(u, v) ↦ (h u * cos v, h u * sin v, ∫ t in 0..u, √(1 - h' t ^ 2))` into `ℝ³`,
which is injective on the strip `ℝ × (0, 2π)`. -/

/-- The canonical continuous linear map `ℝ³ →L[ℝ] EuclideanSpace ℝ (Fin 3)`. -/
