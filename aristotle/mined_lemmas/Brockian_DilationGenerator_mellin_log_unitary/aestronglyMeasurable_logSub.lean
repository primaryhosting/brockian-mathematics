/-
# Mellin Log Unitary
Category: Gate1 Operator
Target: Brockian.DilationGenerator.mellin_log_unitary
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

open MeasureTheory Set Real

namespace Brockian
namespace DilationGenerator

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The substitution operator `U : (U f)(t) = e^{t/2} · f(eᵗ)`, at the level of functions. -/

theorem aestronglyMeasurable_logSub {f : ℝ → F}
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi (0 : ℝ)))) :
    AEStronglyMeasurable (logSub f) volume :=
  AEStronglyMeasurable.smul
    ((Real.continuous_exp.comp (continuous_id.div_const 2)).aestronglyMeasurable)
    (hf.comp_quasiMeasurePreserving quasiMeasurePreserving_exp)

