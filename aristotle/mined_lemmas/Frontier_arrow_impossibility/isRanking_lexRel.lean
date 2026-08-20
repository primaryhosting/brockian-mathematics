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

/-
# Arrow Impossibility
Category: Frontier Mind
Target: Frontier.arrow_impossibility
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Arrow Impossibility
Category: Frontier Mind
Target: Frontier.arrow_impossibility
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-! ## Rankings (strict total orders) -/

/-- A *ranking* of the alternatives `A` is a strict total order: an irreflexive,
transitive and total (trichotomous) relation.  `r x y` means "`x` is strictly
preferred to `y`". -/
structure IsRanking {A : Type*} (r : A → A → Prop) : Prop where
  irrefl : ∀ x, ¬ r x x
  trans : ∀ {x y z}, r x y → r y z → r x z
  total : ∀ x y, x ≠ y → r x y ∨ r y x

namespace IsRanking

variable {A : Type*} {r : A → A → Prop}


theorem isRanking_lexRel {A : Type*} {base : A → A → Prop} (hb : IsRanking base)
    (pr : A → ℕ) : IsRanking (lexRel base pr) where
  irrefl x := by
    rintro (h | ⟨-, h⟩)
    · exact lt_irrefl _ h
    · exact hb.irrefl x h
  trans := by
    rintro x y z (h1 | ⟨h1, h1'⟩) (h2 | ⟨h2, h2'⟩)
    · exact Or.inl (h1.trans h2)
    · exact Or.inl (h2 ▸ h1)
    · exact Or.inl (h1 ▸ h2)
    · exact Or.inr ⟨h1.trans h2, hb.trans h1' h2'⟩
  total x y hne := by
    rcases lt_trichotomy (pr x) (pr y) with h | h | h
    · exact Or.inl (Or.inl h)
    · rcases hb.total x y hne with hb' | hb'
      · exact Or.inl (Or.inr ⟨h, hb'⟩)
      · exact Or.inr (Or.inr ⟨h.symm, hb'⟩)
    · exact Or.inr (Or.inl h)

