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

lemma toLogLp_add (F G : Lp E 2 (volume.restrict (Ioi (0 : ℝ)))) :
    toLogLp (F + G) = toLogLp F + toLogLp G := by
  refine Lp.ext_iff.2 ?_
  have h1 : (toLogLp (F + G) : ℝ → E) =ᵐ[volume] toLog ((F : ℝ → E) + (G : ℝ → E)) :=
    (coeFn_toLogLp _).trans (toLog_congr_ae (Lp.coeFn_add F G))
  have h2 : ((toLogLp F + toLogLp G : Lp E 2 (volume : Measure ℝ)) : ℝ → E)
      =ᵐ[volume] toLog (F : ℝ → E) + toLog (G : ℝ → E) :=
    (Lp.coeFn_add _ _).trans ((coeFn_toLogLp F).add (coeFn_toLogLp G))
  rw [toLog_add] at h1
  exact h1.trans h2.symm

