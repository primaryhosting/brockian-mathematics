import Mathlib
/-!
# Symmetric On Core
Category: Gate1 Operator
Target: Brockian.DilationGenerator.symmetric_on_core
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Complex

namespace Brockian
namespace DilationGenerator

variable {f g : ℝ → ℂ}

/-- The bilinear "boundary weight" `x ↦ x * f x * conj (g x)`, whose derivative is exactly the
combination of terms appearing in the difference of the two sides of the symmetry identity. -/

lemma deriv_weight (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (x : ℝ) :
    deriv (weight f g) x =
      f x * (starRingEnd ℂ) (g x) + (x : ℂ) * deriv f x * (starRingEnd ℂ) (g x)
        + (x : ℂ) * f x * (starRingEnd ℂ) (deriv g x) := by
  have h1 : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := by
    simpa using Complex.ofRealCLM.hasDerivAt
  have h2 : HasDerivAt f (deriv f x) x :=
    (hf.differentiable (by norm_num) x).hasDerivAt
  have h3 : HasDerivAt (fun y : ℝ => (starRingEnd ℂ) (g y)) ((starRingEnd ℂ) (deriv g x)) x := by
    simpa using ((hg.differentiable (by norm_num) x).hasDerivAt).star
  have hd : HasDerivAt (fun y : ℝ => (y : ℂ) * f y * (starRingEnd ℂ) (g y))
      ((1 * f x + (x : ℂ) * deriv f x) * (starRingEnd ℂ) (g x)
        + (x : ℂ) * f x * (starRingEnd ℂ) (deriv g x)) x := (h1.mul h2).mul h3
  have hw : weight f g = fun y : ℝ => (y : ℂ) * f y * (starRingEnd ℂ) (g y) := rfl
  rw [hw, hd.deriv]
  ring

/-- The integral over `(0, ∞)` of the derivative of the boundary weight vanishes: the weight is
`C^1` with compact support and vanishes at `0`. -/
