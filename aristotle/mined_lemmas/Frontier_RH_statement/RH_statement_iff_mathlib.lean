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
# RH Statement
Category: Frontier — Moonshot
Target: Frontier.RH_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex

namespace Frontier

/-- `s` is a *nontrivial zero* of the Riemann zeta function if `ζ s = 0` and `s` is not one of
the *trivial zeros* `-2, -4, -6, …`. -/

theorem RH_statement_iff_mathlib : RiemannHypothesisStatement ↔ RiemannHypothesis := by
  constructor
  · intro h s hz hnt _
    exact h s ⟨hz, fun n hn => hnt ⟨n, hn⟩⟩
  · intro h s hs
    exact h s hs.1 (fun ⟨n, hn⟩ => hs.2 n hn) hs.ne_one

end Frontier

-- Axiom check (should list only `propext`, `Classical.choice`, `Quot.sound`).
#print axioms Frontier.RH_statement
#print axioms Frontier.RH_statement_iff_mathlib
#print axioms Frontier.IsNontrivialZero.re_mem_Ioo
#print axioms Frontier.zeta_neg_odd_ne_zero

