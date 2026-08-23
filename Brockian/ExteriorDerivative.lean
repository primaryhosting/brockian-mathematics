import Mathlib.Analysis.Calculus.DifferentialForm.Basic

/-!
# Exterior-calculus adapter on normed model spaces

This module gives the manifold work a small, explicit interface to Mathlib's current exterior
derivative API.  The forms here live on a normed vector space, not on an arbitrary manifold:

`ModelForm 𝕜 E F n = E → E [⋀^Fin n]→L[𝕜] F`.

The smoothness assumptions are preserved in the public statements.  In particular, `d² = 0`
uses `ContDiff 𝕜 r` with `minSmoothness 𝕜 2 ≤ r`.  No de Rham complex or quasi-isomorphism is
claimed here.
-/

open ContinuousAlternatingMap

namespace Brockian.ExteriorDerivative

variable {𝕜 E F G : Type*}
  [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- An unbundled `n`-form on a normed model vector space. -/
abbrev ModelForm (𝕜 E F : Type*) [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] (n : ℕ) :=
  E → E [⋀^Fin n]→L[𝕜] F

/-- A model-space differential form is closed when its exterior derivative vanishes. -/
def IsClosed {n : ℕ} (ω : ModelForm 𝕜 E F n) : Prop := extDeriv ω = 0

/-- A model-space differential form is exact when it is an exterior derivative. -/
def IsExact {n : ℕ} (η : ModelForm 𝕜 E F (n + 1)) : Prop :=
  ∃ ω : ModelForm 𝕜 E F n, η = extDeriv ω

/-- Mathlib's square-zero theorem, exposed with the model-space boundary and hypotheses visible. -/
theorem extDeriv_sq_zero {n : ℕ} {r : WithTop ℕ∞} {ω : ModelForm 𝕜 E F n}
    (hω : ContDiff 𝕜 r ω) (hr : minSmoothness 𝕜 2 ≤ r) :
    extDeriv (extDeriv ω) = 0 :=
  extDeriv_extDeriv hω hr

/-- The exterior derivative of a sufficiently smooth form is closed. -/
theorem extDeriv_isClosed {n : ℕ} {r : WithTop ℕ∞} {ω : ModelForm 𝕜 E F n}
    (hω : ContDiff 𝕜 r ω) (hr : minSmoothness 𝕜 2 ≤ r) :
    IsClosed (extDeriv ω) :=
  extDeriv_sq_zero hω hr

/-- Exact forms with a sufficiently smooth primitive are closed.  The smoothness of the primitive
is an explicit input, rather than being hidden in the definition of exactness. -/
theorem exact_isClosed {n : ℕ} {r : WithTop ℕ∞} {η : ModelForm 𝕜 E F (n + 1)}
    (hη : ∃ ω : ModelForm 𝕜 E F n, ContDiff 𝕜 r ω ∧ η = extDeriv ω)
    (hr : minSmoothness 𝕜 2 ≤ r) : IsClosed η := by
  obtain ⟨ω, hω, rfl⟩ := hη
  exact extDeriv_isClosed hω hr

/-- Pull back a model-space form using the Fréchet derivative of the map. -/
noncomputable def pullback {n : ℕ} (f : E → F) (ω : ModelForm 𝕜 F G n) :
    ModelForm 𝕜 E G n :=
  fun x ↦ (ω (f x)).compContinuousLinearMap (fderiv 𝕜 f x)

/-- Exterior differentiation commutes pointwise with model-space pullback. -/
theorem extDeriv_pullback_apply {n : ℕ} {r : WithTop ℕ∞} (f : E → F)
    (ω : ModelForm 𝕜 F G n) (x : E) (hω : DifferentiableAt 𝕜 ω (f x))
    (hf : ContDiffAt 𝕜 r f x) (hr : minSmoothness 𝕜 2 ≤ r) :
    extDeriv (pullback f ω) x = pullback f (extDeriv ω) x := by
  exact extDeriv_pullback hω hf hr

/-- Pullback preserves closed forms under the differentiability assumptions required by
Mathlib's naturality theorem. -/
theorem pullback_isClosed {n : ℕ} {r : WithTop ℕ∞} (f : E → F)
    (ω : ModelForm 𝕜 F G n) (hω : Differentiable 𝕜 ω) (hf : ContDiff 𝕜 r f)
    (hr : minSmoothness 𝕜 2 ≤ r) (hc : IsClosed ω) : IsClosed (pullback f ω) := by
  funext x
  rw [extDeriv_pullback_apply f ω x (hω (f x)) hf.contDiffAt hr]
  have hx : extDeriv ω (f x) = 0 := congrFun hc (f x)
  simp [pullback, hx]

/-- Pullback preserves exactness when the chosen primitive satisfies the differentiability
hypothesis of the pullback-naturality theorem. -/
theorem pullback_isExact {n : ℕ} {r : WithTop ℕ∞} (f : E → F)
    (ω : ModelForm 𝕜 F G n) (hω : Differentiable 𝕜 ω) (hf : ContDiff 𝕜 r f)
    (hr : minSmoothness 𝕜 2 ≤ r) : IsExact (pullback f (extDeriv ω)) := by
  refine ⟨pullback f ω, ?_⟩
  funext x
  exact (extDeriv_pullback_apply f ω x (hω (f x)) hf.contDiffAt hr).symm

end Brockian.ExteriorDerivative
