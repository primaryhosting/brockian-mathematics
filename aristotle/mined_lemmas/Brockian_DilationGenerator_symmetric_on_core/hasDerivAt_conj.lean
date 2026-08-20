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

lemma hasDerivAt_conj {g : ℝ → ℂ} {x : ℝ} (h : HasDerivAt g (deriv g x) x) :
    HasDerivAt (fun y => (starRingEnd ℂ) (g y)) ((starRingEnd ℂ) (deriv g x)) x := by
  simpa using (Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt x h)

