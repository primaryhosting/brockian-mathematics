/-
# Knaster Tarski
Category: Computer Science
Target: CS.knaster_tarski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 does not allow a module docstring `/-! ... -/` before `import`,
-- so the required header is kept verbatim as an ordinary block comment.)

import Mathlib

namespace CS

/-- **Knaster–Tarski**: a monotone map `f` on a complete lattice has a least fixed point,
i.e. there is `a` with `f a = a` such that `a ≤ b` for every fixed point `b`.

The witness is `OrderHom.lfp ⟨f, hf⟩` from Mathlib; the key facts used are
`OrderHom.map_lfp` (`f (lfp f) = lfp f`) and `OrderHom.lfp_le` (`f b ≤ b → lfp f ≤ b`). -/
theorem knaster_tarski {α : Type*} [CompleteLattice α] (f : α → α) (hf : Monotone f) :
    ∃ a : α, f a = a ∧ ∀ b : α, f b = b → a ≤ b :=
  ⟨OrderHom.lfp ⟨f, hf⟩, OrderHom.map_lfp ⟨f, hf⟩, fun _ hb => OrderHom.lfp_le _ hb.le⟩

end CS

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

