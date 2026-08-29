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

theorem mellin_log_unitary_inv (h : ℝ → E) :
    ∫ t : ℝ, ‖h t‖ ^ 2
      = ∫ x in Ioi (0 : ℝ), ‖(x ^ (-(1 : ℝ) / 2)) • h (Real.log x)‖ ^ 2 := by
  have key := mellin_log_unitary (mellinLogMapInv h)
  have hcongr : ∀ t : ℝ, ‖Real.exp (t / 2) • mellinLogMapInv h (Real.exp t)‖ ^ 2 = ‖h t‖ ^ 2 := by
    intro t
    rw [show Real.exp (t / 2) • mellinLogMapInv h (Real.exp t) = mellinLogMap
      (mellinLogMapInv h) t from rfl, mellinLogMap_mellinLogMapInv]
  rw [integral_congr_ae (Filter.Eventually.of_forall hcongr)] at key
  exact key.symm

/-- `f` is `L²` on `(0,∞)` if and only if `U f` is `L²` on `ℝ`. -/
