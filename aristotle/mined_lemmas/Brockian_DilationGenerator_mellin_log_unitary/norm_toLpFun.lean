import Mathlib

/-!
# Mellin Log Unitary
Category: Gate1 Operator
Target: Brockian.DilationGenerator.mellin_log_unitary
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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The substitution `x = exp t` as an identity of Lebesgue (`ℝ≥0∞`-valued) integrals:
integrating over `(0, ∞)` is the same as integrating `exp t • ·` over all of `ℝ`. -/

lemma norm_toLpFun (f : Lp E 2 (volume.restrict (Ioi (0 : ℝ)))) : ‖toLpFun f‖ = ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def,
    eLpNorm_congr_ae (coeFn_toLpFun f), eLpNorm_mellinLog]

/-- **The Mellin logarithmic substitution as a unitary.**
The substitution `x = e^t` induces a surjective linear isometry
`U : L²(0, ∞) ≃ L²(ℝ)`, `(U f)(t) = e^{t/2} • f (e^t)`, with inverse
`(U⁻¹ h)(x) = x^{-1/2} • h (log x)`. -/
