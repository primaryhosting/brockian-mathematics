import Mathlib

/-!
# Dilworth
Category: Pure Mathematics
Target: Math.dilworth
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Classical

namespace Math

variable {α : Type*} [Fintype α] [PartialOrder α]

/-- The largest cardinality of a chain contained in the finite set `t`. -/

lemma antichain_level (i : ℕ) :
    IsAntichain (· ≤ ·) ((Finset.univ.filter fun x : α => height x = i : Finset α) : Set α) := by
  intro x hx y hy hne hle
  simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hx hy
  have : x < y := lt_of_le_of_ne hle hne
  have := height_lt_height this
  omega

/-- Every antichain cover has at least as many members as the longest chain. -/
