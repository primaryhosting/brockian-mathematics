import Mathlib

/-!
# Symmetric On Core
Category: Gate1 Operator
Target: Brockian.DilationGenerator.symmetric_on_core
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-- Auxiliary product `x ↦ x · f x · conj (g x)` whose derivative encodes the
integration-by-parts identity for the Berry–Keating dilation generator. -/

lemma hasDerivAt_prodAux {f g : ℝ → ℂ} (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (x : ℝ) :
    HasDerivAt (prodAux f g)
      (f x * (starRingEnd ℂ) (g x) + (x : ℂ) * deriv f x * (starRingEnd ℂ) (g x)
        + (x : ℂ) * f x * (starRingEnd ℂ) (deriv g x)) x := by
  have hx : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := by
    simpa using Complex.ofRealCLM.hasDerivAt (x := x)
  have hfx : HasDerivAt f (deriv f x) x := (hf.differentiable (by simp) x).hasDerivAt
  have hgx : HasDerivAt g (deriv g x) x := (hg.differentiable (by simp) x).hasDerivAt
  have hcg := hasDerivAt_conj hgx
  have h1 : HasDerivAt (fun y : ℝ => (y : ℂ) * f y) (1 * f x + (x : ℂ) * deriv f x) x :=
    hx.mul hfx
  have h2 := h1.mul hcg
  convert h2 using 1
  ring

