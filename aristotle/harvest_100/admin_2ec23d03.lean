/-
# Knaster Tarski
Category: Computer Science
Target: CS.knaster_tarski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` to precede any module doc-comment `/-! ... -/`,
-- so the header above is a plain block comment and is repeated verbatim
-- as a module doc-comment immediately after the imports.)

import Mathlib

/-!
# Knaster Tarski
Category: Computer Science
Target: CS.knaster_tarski
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

namespace CS

/-- **Knaster–Tarski**: a monotone map `f` on a complete lattice has a least fixed point.
The witness is `OrderHom.lfp`, and the two facts used are Mathlib's
`OrderHom.map_lfp` (`f (lfp f) = lfp f`) and `OrderHom.lfp_le`
(`f a ≤ a → lfp f ≤ a`). -/
theorem knaster_tarski {α : Type*} [CompleteLattice α] (f : α → α) (hf : Monotone f) :
    IsLeast {a : α | f a = a} (OrderHom.lfp ⟨f, hf⟩) := by
  constructor
  · exact OrderHom.map_lfp ⟨f, hf⟩
  · intro b hb
    exact OrderHom.lfp_le _ hb.le

end CS

