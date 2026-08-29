import Mathlib

/-!
# RH Statement
Category: Frontier — Moonshot
Target: Frontier.RH_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex
open scoped Real

namespace Frontier

/-- `s` is a *trivial* zero of the Riemann zeta function, i.e. `s = -2, -4, -6, …`. -/

theorem riemannHypothesisStatement_iff_riemannHypothesis :
    RiemannHypothesisStatement ↔ RiemannHypothesis := by
  constructor
  · intro h s hz hnt _
    exact h s ⟨hz, hnt⟩
  · intro h s ⟨hz, hnt⟩
    refine h s hz hnt ?_
    rintro rfl
    exact absurd hz (riemannZeta_ne_zero_of_one_le_re (by simp))

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

