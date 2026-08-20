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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian
namespace DilationGenerator

/-- The pointwise product `x ↦ x · f x · conj (g x)`, whose derivative encodes the
integration-by-parts identity for the Berry–Keating dilation generator. -/

theorem hasDerivAt_pairing {f g : ℝ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (x : ℝ) :
    HasDerivAt (pairing f g)
      (f x * starRingEnd ℂ (g x) +
        (x : ℂ) * (deriv f x * starRingEnd ℂ (g x) +
          f x * starRingEnd ℂ (deriv g x))) x := by
  have hx : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 x := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := x))
  have hfd : HasDerivAt f (deriv f x) x :=
    (hf.differentiable (by norm_num) x).hasDerivAt
  have hgd : HasDerivAt g (deriv g x) x :=
    (hg.differentiable (by norm_num) x).hasDerivAt
  have hgs : HasDerivAt (fun t : ℝ => starRingEnd ℂ (g t)) (starRingEnd ℂ (deriv g x)) x := by
    simpa [Complex.star_def] using hgd.star
  have := hx.mul (hfd.mul hgs)
  simpa [pairing, one_mul] using this

/-- `pairing f g` is `C^1`. -/
