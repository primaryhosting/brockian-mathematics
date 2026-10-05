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

open MeasureTheory

/-- The auxiliary function `x ↦ x · f(x) · conj(g(x))`, whose derivative is exactly the
integrand appearing in the difference of the two sides of the symmetry identity. -/

theorem hasDerivAt_pairing {f g : ℝ → ℂ} {x : ℝ}
    (hf : HasDerivAt f (deriv f x) x) (hg : HasDerivAt g (deriv g x) x) :
    HasDerivAt (pairing f g)
      ((1 * f x + (x : ℂ) * deriv f x) * (starRingEnd ℂ) (g x)
        + ((x : ℂ) * f x) * (starRingEnd ℂ) (deriv g x)) x := by
  have hx : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 x := by
    simpa using Complex.ofRealCLM.hasDerivAt (x := x)
  exact (hx.mul hf).mul hg.star

