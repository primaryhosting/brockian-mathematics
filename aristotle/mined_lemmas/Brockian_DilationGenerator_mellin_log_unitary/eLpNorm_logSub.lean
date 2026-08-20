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

theorem eLpNorm_logSub (f : ℝ → F) :
    eLpNorm (logSub f) 2 volume = eLpNorm f 2 (volume.restrict (Ioi (0 : ℝ))) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    lintegral_Ioi_eq_lintegral_exp_mul (fun x => ‖f x‖ₑ ^ (2 : ENNReal).toReal)]
  congr 1
  refine lintegral_congr fun t => ?_
  rw [logSub, enorm_smul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  congr 1
  rw [Real.enorm_eq_ofReal (Real.exp_pos _).le, ENNReal.ofReal_rpow_of_pos (Real.exp_pos _)]
  congr 1
  rw [show (2 : ENNReal).toReal = (2 : ℝ) by norm_num, ← Real.exp_mul]
  ring_nf

/-- `U⁻¹` preserves the `L²` norm. -/
