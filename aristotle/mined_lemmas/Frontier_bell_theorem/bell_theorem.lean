/-
# Bell Theorem
Category: Frontier Physics
Target: Frontier.bell_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Bell Theorem
Category: Frontier Physics
Target: Frontier.bell_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory

namespace Frontier

/-- Pointwise CHSH inequality: for outcomes in `[-1, 1]`, the CHSH combination is
bounded by `2`. -/

theorem bell_theorem :
    ¬ ∃ (Ω : Type) (_ : MeasurableSpace Ω) (M : LHVModel Ω),
        M.corr 0 0 = Real.sqrt 2 / 2 ∧ M.corr 0 1 = Real.sqrt 2 / 2 ∧
        M.corr 1 0 = Real.sqrt 2 / 2 ∧ M.corr 1 1 = -(Real.sqrt 2 / 2) := by
  rintro ⟨Ω, _, M, h00, h01, h10, h11⟩
  have hbound := chsh_le_two M
  have hval : M.chsh = 2 * Real.sqrt 2 := by
    simp only [LHVModel.chsh, h00, h01, h10, h11]; ring
  rw [hval, abs_of_nonneg (by positivity)] at hbound
  linarith [quantum_chsh_value.2]

end Frontier

#print axioms Frontier.bell_theorem
#print axioms Frontier.chsh_le_two

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

