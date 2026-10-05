/-
# Pigeonhole
Category: Frontier Wave 2 (deeper machinery)
Target: Combinatorics.pigeonhole
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-!
# Pigeonhole
Category: Frontier Wave 2 (deeper machinery)
Target: Combinatorics.pigeonhole
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Combinatorics

/-- **Pigeonhole principle** (type version): if `f : α → β` with `α`, `β` finite types and
`Fintype.card β < Fintype.card α`, then `f` is not injective, i.e. there are two distinct
elements of `α` with the same image. -/

theorem pigeonhole_finset {α β : Type*} [DecidableEq β] {s : Finset α} {t : Finset β}
    (f : α → β) (hf : ∀ a ∈ s, f a ∈ t) (h : t.card < s.card) :
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ f a = f b :=
  Finset.exists_ne_map_eq_of_card_lt_of_maps_to h hf

end Combinatorics

