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

theorem memLp_mellinLogMap_iff (f : ℝ → E) (hf : AEStronglyMeasurable f
    (volume.restrict (Ioi (0 : ℝ)))) (hUf : AEStronglyMeasurable (mellinLogMap f) volume) :
    MemLp (mellinLogMap f) 2 volume ↔ MemLp f 2 (volume.restrict (Ioi (0 : ℝ))) := by
  constructor
  · intro hm
    exact ⟨hf, by rw [← eLpNorm_mellinLogMap]; exact hm.2⟩
  · intro hm
    exact ⟨hUf, by rw [eLpNorm_mellinLogMap]; exact hm.2⟩

end DilationGenerator
end Brockian

