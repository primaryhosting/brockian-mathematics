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
# Ramsey 3 5
Category: Pure Mathematics
Target: Math.ramsey_3_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Ramsey 3 5
Category: Pure Mathematics
Target: Math.ramsey_3_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset SimpleGraph

namespace Math

/-! ## The Ramsey property -/

/-- `RamseyProp n s t` says: every simple graph on `n` vertices contains either a clique of
size `s`, or an independent set of size `t` (a clique of size `t` in the complement).
Equivalently, every 2-colouring of the edges of `K n` has a red `K s` or a blue `K t`. -/

lemma isClique_of_cliqueFreeOn_two {B : Finset V} (h : Gᶜ.CliqueFreeOn (↑B) 2) :
    G.IsClique (↑B) := by
  intro x hx y hy hxy
  by_contra hadj
  refine h (t := {x, y}) ?_ ?_
  · intro z hz
    simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl <;> assumption
  · rw [SimpleGraph.isNClique_iff]
    constructor
    · intro a ha b hb hab
      simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
      have : ∀ p q : V, p = x ∨ p = y → q = x ∨ q = y → p ≠ q → Gᶜ.Adj p q := by
        rintro p q (rfl | rfl) (rfl | rfl) hpq
        · exact absurd rfl hpq
        · exact ⟨hpq, hadj⟩
        · exact ⟨hpq, fun h' => hadj h'.symm⟩
        · exact absurd rfl hpq
      exact this a b ha hb hab
    · rw [Finset.card_insert_of_notMem (by simpa using hxy), Finset.card_singleton]

/-- In a triangle-free graph, the neighbourhood of a vertex is independent. -/
