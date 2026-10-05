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

open scoped Real ENNReal
open MeasureTheory Set

namespace Brockian
namespace DilationGenerator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The image of `ℝ` under `exp` is the positive half line. -/

theorem lintegral_enorm_sq_mellinLogMap (f : ℝ → E) :
    ∫⁻ x in Ioi (0 : ℝ), ‖f x‖ₑ ^ 2 = ∫⁻ t : ℝ, ‖mellinLogMap f t‖ₑ ^ 2 := by
  rw [lintegral_comp_exp (fun x => ‖f x‖ₑ ^ 2)]
  refine lintegral_congr (fun t => ?_)
  have h1 : ‖mellinLogMap f t‖ₑ ^ 2 = ENNReal.ofReal (‖mellinLogMap f t‖ ^ 2) := by
    rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  have h2 : ‖f (Real.exp t)‖ₑ ^ 2 = ENNReal.ofReal (‖f (Real.exp t)‖ ^ 2) := by
    rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  rw [h1, h2, norm_sq_mellinLogMap, ENNReal.ofReal_mul (Real.exp_pos t).le]

/-- The `L²` norm (as an `eLpNorm`) is preserved by `U`: this is the "unitarity" statement at the
level of norms. -/
