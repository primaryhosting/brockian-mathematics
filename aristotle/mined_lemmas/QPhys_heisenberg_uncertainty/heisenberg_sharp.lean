import Mathlib

/-!
# Heisenberg Uncertainty
Category: Quantum Physics
Target: QPhys.heisenberg_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped InnerProductSpace

namespace QPhys

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The uncertainty (standard deviation) of a symmetric operator `A` in the state `ψ`:
the norm of `A ψ` after subtracting its expectation value `⟪ψ, A ψ⟫`. -/

theorem heisenberg_sharp :
    uncertainty sigmaX up * uncertainty sigmaY up = (2 : ℝ) / 2 := by
  rw [uncertainty_sigmaX, uncertainty_sigmaY]; norm_num

/-- Sanity check: the general theorem applies to this model. -/
example : uncertainty sigmaX up * uncertainty sigmaY up ≥ (2 : ℝ) / 2 :=
  heisenberg_uncertainty sigmaX sigmaY up norm_up sigmaX_symm sigmaY_symm 2 commutator_up

end SpinExample

end QPhys

import Mathlib
import RequestProject.Heisenberg

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

