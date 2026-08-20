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

import Mathlib

/-!
# Mellin Log Unitary
Category: Gate1 Operator
Target: Brockian.DilationGenerator.mellin_log_unitary
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Set Real
open scoped ENNReal NNReal

namespace Brockian.DilationGenerator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The substitution `x = exp t` maps `ℝ` onto `(0, ∞)`. -/

theorem memLp_ofLog {h : ℝ → E} (hh : MemLp h 2 volume) :
    MemLp (ofLog h) 2 (volume.restrict (Ioi (0 : ℝ))) :=
  ⟨aestronglyMeasurable_ofLog hh.1, by rw [eLpNorm_ofLog]; exact hh.2⟩

/-! ### The unitary `L²(0, ∞) ≃ L²(ℝ)` -/

/-- The image in `L²(ℝ)` of an element of `L²(0, ∞)` under `f ↦ (t ↦ e^{t/2} f(e^t))`. -/
