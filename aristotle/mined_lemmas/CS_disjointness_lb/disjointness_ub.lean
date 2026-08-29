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

import Mathlib

/-!
# Disjointness Lb
Category: Frontier Cs
Target: CS.disjointness_lb
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

universe u v

/-- A deterministic two-party communication protocol: a binary tree whose internal nodes
are labelled either by a bit that Alice sends (a function of her input `x : X`) or by a bit
that Bob sends (a function of his input `y : Y`), and whose leaves carry the output bit. -/
inductive Protocol (X : Type u) (Y : Type v) : Type (max u v)
  | leaf : Bool → Protocol X Y
  | alice : (X → Bool) → Protocol X Y → Protocol X Y → Protocol X Y
  | bob : (Y → Bool) → Protocol X Y → Protocol X Y → Protocol X Y

namespace Protocol

variable {X : Type u} {Y : Type v}

/-- The communication cost of a protocol: the depth of the tree, i.e. the worst-case number
of bits exchanged. -/

theorem disjointness_ub (n : ℕ) :
    ∃ p : Protocol (Finset (Fin n)) (Finset (Fin n)),
      (∀ S T : Finset (Fin n), p.run S T = Disj n S T) ∧ p.cost = n + 1 := by
  refine ⟨Protocol.build (List.finRange n) ∅, ?_, ?_⟩
  · intro S T
    rw [Protocol.run_build]
    have : S.filter (fun x => x ∈ List.finRange n) = S := by
      apply Finset.filter_true_of_mem
      intro x _
      simp
    rw [this, Finset.empty_union]
  · rw [Protocol.cost_build, List.length_finRange]

end CS

