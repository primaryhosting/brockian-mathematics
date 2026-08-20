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

theorem inverse_right_inv (h : ℝ → E) (t : ℝ) :
    Real.exp (t / 2) •
        ((Real.exp t) ^ (-(1 : ℝ) / 2) • h (Real.log (Real.exp t))) = h t := by
  rw [Real.log_exp, smul_smul, Real.rpow_def_of_pos (Real.exp_pos t), Real.log_exp,
    ← Real.exp_add]
  have hz : t / 2 + t * (-(1 : ℝ) / 2) = 0 := by ring
  rw [hz, Real.exp_zero, one_smul]


/-! ### Measure-theoretic form of the substitution -/

/-- The density `e^t` appearing in the change of variables `x = e^t`. -/
