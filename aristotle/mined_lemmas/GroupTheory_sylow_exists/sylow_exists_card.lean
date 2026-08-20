/-
# Sylow Exists
Category: Frontier Wave 2 (deeper machinery)
Target: GroupTheory.sylow_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sylow Exists
Category: Frontier Wave 2 (deeper machinery)
Target: GroupTheory.sylow_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace GroupTheory

/-- **Sylow's first theorem** (existence form): for a finite group `G` and a prime `p`,
a Sylow `p`-subgroup of `G` exists, i.e. the type `Sylow p G` is nonempty.

This follows from Mathlib's `Sylow.nonempty` instance (itself a consequence of
`IsPGroup.exists_le_sylow`, proved by Zorn's lemma).

Note: the hypotheses `[Fintype G]` and `hp : p.Prime` were requested in the statement but
are in fact not needed — Mathlib's `Sylow.nonempty` holds for an arbitrary group and an
arbitrary natural number `p`. They are retained here for faithfulness to the request. -/

theorem sylow_exists_card (G : Type*) [Group G] [Fintype G] (p : ℕ) (hp : p.Prime) :
    ∃ P : Subgroup G, Nat.card P = p ^ (Nat.card G).factorization p := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨P⟩ := sylow_exists G p hp
  exact ⟨P.toSubgroup, P.card_eq_multiplicity⟩

end GroupTheory

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

