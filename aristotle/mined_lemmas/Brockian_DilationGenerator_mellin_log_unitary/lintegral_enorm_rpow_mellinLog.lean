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

lemma lintegral_enorm_rpow_mellinLog (f : ℝ → E) :
    ∫⁻ t : ℝ, ‖mellinLog f t‖ₑ ^ (2 : ℝ)
      = ∫⁻ x in Ioi (0 : ℝ), ‖f x‖ₑ ^ (2 : ℝ) := by
  rw [lintegral_Ioi_eq_lintegral_exp_smul (fun x => ‖f x‖ₑ ^ (2 : ℝ))]
  refine lintegral_congr fun t => ?_
  have hpos : (0 : ℝ) < Real.exp (t / 2) := Real.exp_pos _
  have hsq : Real.exp (t / 2) ^ (2 : ℝ) = Real.exp t := by
    rw [Real.rpow_def_of_pos hpos, Real.log_exp]
    ring_nf
  rw [mellinLog, enorm_smul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2),
    Real.enorm_eq_ofReal hpos.le, ENNReal.ofReal_rpow_of_pos hpos, hsq]

