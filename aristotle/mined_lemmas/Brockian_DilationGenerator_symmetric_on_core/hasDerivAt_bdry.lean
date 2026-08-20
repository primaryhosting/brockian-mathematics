/-
# Symmetric On Core
Category: Gate1 Operator
Target: Brockian.DilationGenerator.symmetric_on_core
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian
namespace DilationGenerator

open MeasureTheory Complex

/-- The auxiliary "boundary" function `x ↦ i · x · f x · conj (g x)`, whose derivative is
exactly the difference of the two integrands. -/
private noncomputable def bdry (f g : ℝ → ℂ) : ℝ → ℂ :=
  fun x => Complex.I * (x : ℂ) * f x * (starRingEnd ℂ) (g x)


private theorem hasDerivAt_bdry {f g : ℝ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (x : ℝ) :
    HasDerivAt (bdry f g)
      (Complex.I * (f x * (starRingEnd ℂ) (g x)
        + (x : ℂ) * (deriv f x * (starRingEnd ℂ) (g x)
          + f x * (starRingEnd ℂ) (deriv g x)))) x := by
  have hfd : HasDerivAt f (deriv f x) x :=
    (hf.differentiable (by simp) x).hasDerivAt
  have hgd : HasDerivAt g (deriv g x) x :=
    (hg.differentiable (by simp) x).hasDerivAt
  have hgc : HasDerivAt (fun y : ℝ => (starRingEnd ℂ) (g y)) ((starRingEnd ℂ) (deriv g x)) x :=
    hgd.star
  have hx : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := Complex.ofRealCLM.hasDerivAt
  have h1 : HasDerivAt (fun y : ℝ => Complex.I * (y : ℂ)) (Complex.I * 1) x :=
    hx.const_mul Complex.I
  have h2 := (h1.mul hfd).mul hgc
  refine HasDerivAt.congr_deriv (f := bdry f g) h2 ?_
  simp only [Pi.mul_apply]
  ring

/-- **Symmetry of the Berry–Keating dilation generator on the smooth compactly supported core.**

For `f, g : ℝ → ℂ` smooth with compact support contained in `(0, ∞)`,
`∫ (A f) · conj g = ∫ f · conj (A g)` on `(0, ∞)`, where `A f = i·((1/2)·f + x·f')`.

This is symmetry on the core only; no self-adjointness is claimed.

Note: the hypotheses `HasCompactSupport g`, `tsupport f ⊆ Set.Ioi 0` and `tsupport g ⊆ Set.Ioi 0`,
which are part of the requested statement, turn out not to be needed for the proof (the boundary
term at `0` vanishes because of the factor `x`, and compact support of `f` alone already makes all
integrands compactly supported); they are kept because they describe the intended core. -/
