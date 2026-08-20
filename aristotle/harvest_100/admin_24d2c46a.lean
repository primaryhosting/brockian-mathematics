/-
# Pigeonhole Hash
Category: Computer Science
Target: CS.pigeonhole_hash
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean requires `import` to come first in a file, and a module docstring
`/-! ... -/` may not precede it. The header above is therefore rendered as a
plain block comment; the same text is repeated as a module docstring below.)
-/

import Mathlib

/-!
# Pigeonhole Hash
Category: Computer Science
Target: CS.pigeonhole_hash
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

/-- **Pigeonhole hash**: any hash function from a set of `n + 1` keys to a set of
`n` buckets has a collision, i.e. two distinct keys mapping to the same bucket. -/
theorem pigeonhole_hash (n : ℕ) (h : Fin (n + 1) → Fin n) :
    ∃ a b : Fin (n + 1), a ≠ b ∧ h a = h b := by
  have hcard : Fintype.card (Fin n) < Fintype.card (Fin (n + 1)) := by simp
  obtain ⟨a, b, hab, hfab⟩ := Fintype.exists_ne_map_eq_of_card_lt h hcard
  exact ⟨a, b, hab, hfab⟩

/-- General form: any map from a finite type `α` to a finite type `β` with
`Fintype.card β < Fintype.card α` has a collision. -/
theorem pigeonhole_hash_general {α β : Type*} [Fintype α] [Fintype β]
    (h : α → β) (hlt : Fintype.card β < Fintype.card α) :
    ∃ a b : α, a ≠ b ∧ h a = h b :=
  Fintype.exists_ne_map_eq_of_card_lt h hlt

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

