import Mathlib

/-!
# RH Statement
Category: Frontier — Moonshot
Target: Frontier.RH_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on the header: Lean 4 requires `import` lines to be the very first commands in a file,
so the module docstring above is placed directly after `import Mathlib` (a `/-! ... -/` block
before the imports is rejected by the parser).
-/

open Complex

namespace Frontier

/-- `s` is a *trivial zero* of the Riemann zeta function if it is one of the points
`-2, -4, -6, …`, at which `ζ` is known to vanish (`riemannZeta_neg_two_mul_nat_add_one`). -/

theorem RH_statement_iff_mathlib : RH_statement ↔ RiemannHypothesis := by
  constructor
  · intro h s hz hnt _
    exact h s ⟨hz, hnt⟩
  · intro h s hs
    refine h s hs.1 hs.2 ?_
    rintro rfl
    exact riemannZeta_ne_zero_of_one_le_re (by simp) hs.1

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

