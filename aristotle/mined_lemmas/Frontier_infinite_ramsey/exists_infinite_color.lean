import Mathlib

/-!
# Infinite Ramsey
Category: Frontier — Set Theory
Target: Frontier.infinite_ramsey
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

namespace Frontier

/-- A two-valued splitting lemma: if a set is infinite, one of the two colour classes
determined by a `Bool`-valued function is infinite. -/

lemma exists_infinite_color (g : ℕ → Bool) : ∃ b : Bool, {k | g k = b}.Infinite := by
  by_contra h
  push_neg at h
  refine Set.infinite_univ (α := ℕ) (((h true).union (h false)).subset ?_)
  intro n _
  cases hb : g n
  · exact Or.inr hb
  · exact Or.inl hb

/-- **Infinite Ramsey theorem for pairs and two colours.**
Every 2-colouring `c` of the unordered pairs of natural numbers (encoded as `c x y` for
`x < y`) admits an infinite set `S` all of whose pairs receive the same colour `b`. -/
