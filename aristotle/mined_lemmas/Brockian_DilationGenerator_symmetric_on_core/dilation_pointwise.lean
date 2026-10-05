/-
# Symmetric On Core
Category: Gate1 Operator
Target: Brockian.DilationGenerator.symmetric_on_core
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

open MeasureTheory Set

/-- The pointwise algebraic identity behind the symmetry of the Berry–Keating dilation
generator: the two `1/2`-terms together with the cross term of the Leibniz rule combine into
the derivative of `x ↦ x * f x * conj (g x)` (multiplied by `i`). -/

private lemma dilation_pointwise (x : ℝ) (f g df dg : ℂ) :
    (Complex.I * ((1 / 2) * f + x * df)) * starRingEnd ℂ g
        - f * starRingEnd ℂ (Complex.I * ((1 / 2) * g + x * dg))
      = Complex.I *
          (f * starRingEnd ℂ g + (x : ℂ) * (df * starRingEnd ℂ g + f * starRingEnd ℂ dg)) := by
  simp [map_add, map_mul, map_ofNat, Complex.conj_I, Complex.conj_ofReal]
  ring

/-- **Symmetry of the Berry–Keating dilation generator on the smooth compactly supported core.**

For `f, g : ℝ → ℂ` smooth, compactly supported, with supports inside `(0, ∞)`, the operator
`A f = i * ((1/2) * f + x * f')` satisfies `∫ (A f) * conj g = ∫ f * conj (A g)` on `(0, ∞)`.

This is symmetry on the core only; no self-adjointness is claimed.

The proof is integration by parts: the integrand difference equals `i * (d/dx) (x * f * conj g)`,
whose integral over `(0, ∞)` is `- (0 * f 0 * conj (g 0)) = 0` by
`HasCompactSupport.integral_Ioi_deriv_eq`.

(The hypotheses `hfs`, `hgs` on the supports were requested in the statement; the proof does not
need them, since the boundary term vanishes already because of the factor `x`.) -/
