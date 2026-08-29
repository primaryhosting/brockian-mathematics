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


private theorem hasCompactSupport_aux {f g : ℝ → ℂ} (hf : HasCompactSupport f) :
    HasCompactSupport (aux f g) := by
  refine HasCompactSupport.intro (K := tsupport f) hf ?_
  intro x hx
  simp [aux, image_eq_zero_of_notMem_tsupport hx]

/-- **Symmetry of the Berry–Keating dilation generator on the smooth, compactly supported
core of `(0, ∞)`.**

For `f, g : ℝ → ℂ` which are infinitely differentiable, compactly supported, with supports
contained in `(0, ∞)`, the operator `A f = i · ((1/2) f + x f')` satisfies
`∫ (A f) · conj g = ∫ f · conj (A g)` over `(0, ∞)`.

The proof is integration by parts: the integrand difference is exactly
`i · (d/dx) (x · f · conj g)`, and the integral of that derivative over `(0, ∞)` equals
`-(0 · f 0 · conj (g 0)) = 0` by compact support.

Note: the support hypotheses `tsupport f ⊆ (0, ∞)`, `tsupport g ⊆ (0, ∞)` are stated as
requested; the boundary term vanishes already because of the factor `x` at `x = 0`, so these
hypotheses are not needed in the proof.  This is symmetry on the core only, not
self-adjointness.

The smoothness exponent is `((⊤ : ℕ∞) : WithTop ℕ∞)`, i.e. `C^∞`. -/
