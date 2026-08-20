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

namespace Combinatorics

/-- **Pigeonhole principle** (type version): if `f : α → β` with `α`, `β` finite types and
`Fintype.card β < Fintype.card α`, then `f` collides: there are `a ≠ b` with `f a = f b`.
Closed by Mathlib's `Fintype.exists_ne_map_eq_of_card_lt`. -/

theorem pigeonhole_finset {α β : Type*} {s : Finset α} {t : Finset β} (f : α → β)
    (hmaps : ∀ a ∈ s, f a ∈ t) (hcard : t.card < s.card) :
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ f a = f b :=
  Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps

end Combinatorics

