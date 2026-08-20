/-
# Pigeonhole Hash
Category: Computer Science
Target: CS.pigeonhole_hash
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace CS

/-- **Pigeonhole hash.** Any hash function from a set of `n + 1` keys to a set of `n`
buckets has a collision: two distinct keys mapped to the same bucket.

Proved directly from Mathlib's `Fintype.exists_ne_map_eq_of_card_lt`. -/
theorem pigeonhole_hash {α β : Type*} [Fintype α] [Fintype β] {n : ℕ}
    (hα : Fintype.card α = n + 1) (hβ : Fintype.card β = n) (f : α → β) :
    ∃ x y : α, x ≠ y ∧ f x = f y :=
  Fintype.exists_ne_map_eq_of_card_lt f (by omega)

/-- Concrete instance: any `f : Fin (n+1) → Fin n` has a collision. -/
theorem pigeonhole_hash_fin (n : ℕ) (f : Fin (n + 1) → Fin n) :
    ∃ x y : Fin (n + 1), x ≠ y ∧ f x = f y :=
  pigeonhole_hash (n := n) (by simp) (by simp) f

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

