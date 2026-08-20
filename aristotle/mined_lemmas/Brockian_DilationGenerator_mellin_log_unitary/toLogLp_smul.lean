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

lemma toLogLp_smul (c : ℝ) (F : Lp E 2 (volume.restrict (Ioi (0 : ℝ)))) :
    toLogLp (c • F) = c • toLogLp F := by
  refine Lp.ext_iff.2 ?_
  have h1 : (toLogLp (c • F) : ℝ → E) =ᵐ[volume] toLog (c • (F : ℝ → E)) :=
    (coeFn_toLogLp _).trans (toLog_congr_ae (Lp.coeFn_smul c F))
  have h2 : ((c • toLogLp F : Lp E 2 (volume : Measure ℝ)) : ℝ → E)
      =ᵐ[volume] c • toLog (F : ℝ → E) :=
    (Lp.coeFn_smul _ _).trans ((coeFn_toLogLp F).const_smul c)
  rw [toLog_smul] at h1
  exact h1.trans h2.symm

