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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian
namespace DilationGenerator

open MeasureTheory

/-- The auxiliary function `x ↦ x · f x · conj (g x)`, whose derivative packages the
integration-by-parts identity for the Berry–Keating dilation generator. -/
private noncomputable def aux (f g : ℝ → ℂ) : ℝ → ℂ :=
  fun x => (x : ℂ) * f x * starRingEnd ℂ (g x)


private theorem hasDerivAt_aux {f g : ℝ → ℂ} (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (x : ℝ) :
    HasDerivAt (aux f g)
      (f x * starRingEnd ℂ (g x) +
        (x : ℂ) * (deriv f x * starRingEnd ℂ (g x) + f x * starRingEnd ℂ (deriv g x))) x := by
  have hx : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 x := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := x))
  have hfx : HasDerivAt f (deriv f x) x := (hf.differentiable (by simp) x).hasDerivAt
  have hgx : HasDerivAt g (deriv g x) x := (hg.differentiable (by simp) x).hasDerivAt
  have hgc : HasDerivAt (fun t : ℝ => starRingEnd ℂ (g t)) (starRingEnd ℂ (deriv g x)) x := by
    simpa using hgx.star
  have h : HasDerivAt (aux f g)
      ((1 * f x + (x : ℂ) * deriv f x) * starRingEnd ℂ (g x) +
        ((x : ℂ) * f x) * starRingEnd ℂ (deriv g x)) x := (hx.mul hfx).mul hgc
  convert h using 1
  ring

