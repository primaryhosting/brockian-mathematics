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

-- (Lean requires `import` to precede any module docstring, so the header above is repeated
-- verbatim as the module docstring below.)

import Mathlib

/-!
# Arrow Impossibility
Category: Frontier Mind
Target: Frontier.arrow_impossibility
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

variable {A : Type*} {n : ℕ}

/-! ## Rankings and profiles -/

/-- `r` is a strict ranking (irreflexive, transitive, total) of the alternatives. -/
structure IsRanking (r : A → A → Prop) : Prop where
  asymm : ∀ x y, r x y → ¬ r y x
  trans' : ∀ x y z, r x y → r y z → r x z
  total : ∀ x y, x ≠ y → r x y ∨ r y x


lemma isRanking_byRank (rk : A → ℕ) {r : A → A → Prop} (hr : IsRanking r) :
    IsRanking (byRank rk r) where
  asymm := by
    rintro x y (h | ⟨h, hr1⟩) (h' | ⟨h', hr2⟩)
    · omega
    · omega
    · omega
    · exact hr.asymm _ _ hr1 hr2
  trans' := by
    rintro x y z (h | ⟨h, hr1⟩) (h' | ⟨h', hr2⟩)
    · exact Or.inl (by omega)
    · exact Or.inl (by omega)
    · exact Or.inl (by omega)
    · exact Or.inr ⟨by omega, hr.trans' _ _ _ hr1 hr2⟩
  total := by
    intro x y hxy
    rcases lt_trichotomy (rk x) (rk y) with h | h | h
    · exact Or.inl (Or.inl h)
    · rcases hr.total x y hxy with h' | h'
      · exact Or.inl (Or.inr ⟨h, h'⟩)
      · exact Or.inr (Or.inr ⟨h.symm, h'⟩)
    · exact Or.inr (Or.inl h)

/-- Every type carries a ranking. -/
