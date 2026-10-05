/-
# Pigeonhole
Category: Frontier Wave 2 (deeper machinery)
Target: Combinatorics.pigeonhole
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Pigeonhole
Category: Frontier Wave 2 (deeper machinery)
Target: Combinatorics.pigeonhole
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Combinatorics

/-- **The pigeonhole principle.** If `α` and `β` are finite types with
`Fintype.card β < Fintype.card α`, then any `f : α → β` collides: there are
`a ≠ b` with `f a = f b`, and consequently `f` is not injective.

This is Mathlib's `Fintype.exists_ne_map_eq_of_card_lt`. -/
theorem pigeonhole {α β : Type*} [Fintype α] [Fintype β] (f : α → β)
    (h : Fintype.card β < Fintype.card α) :
    (∃ a b : α, a ≠ b ∧ f a = f b) ∧ ¬ Function.Injective f := by
  obtain ⟨a, b, hab, hfab⟩ := Fintype.exists_ne_map_eq_of_card_lt f h
  exact ⟨⟨a, b, hab, hfab⟩, fun hinj => hab (hinj hfab)⟩

end Combinatorics

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

