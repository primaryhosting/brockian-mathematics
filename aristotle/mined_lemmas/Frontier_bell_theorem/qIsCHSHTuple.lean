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

open scoped Real
open MeasureTheory Matrix

namespace Frontier

/-! ## The classical (local hidden variable) side -/

/-- The pointwise CHSH bound: if four numbers `a₀, a₁, b₀, b₁` have absolute value at most `1`
(the possible outcomes, or local averages of outcomes, of `±1`-valued measurements), then the
CHSH combination is bounded by `2` in absolute value. -/

theorem qIsCHSHTuple : IsCHSHTuple (qA 0) (qA 1) (qB 0) (qB 1) where
  A₀_inv := by rw [sq]; exact qA_sq 0
  A₁_inv := by rw [sq]; exact qA_sq 1
  B₀_inv := by rw [sq]; exact qB_sq 0
  B₁_inv := by rw [sq]; exact qB_sq 1
  A₀_sa := qA_symm 0
  A₁_sa := qA_symm 1
  B₀_sa := qB_symm 0
  B₁_sa := qB_symm 1
  A₀B₀_commutes := qA_qB_commute 0 0
  A₀B₁_commutes := qA_qB_commute 0 1
  A₁B₀_commutes := qA_qB_commute 1 0
  A₁B₁_commutes := qA_qB_commute 1 1

end Frontier

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

