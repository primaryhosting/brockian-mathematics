import Mathlib

/-!
# Sorting Lb 5
Category: Computer Science
Target: CS.sorting_lb_5
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
set_option pp.piBinderTypes true

set_option grind.warning false

namespace CS

/-- A comparison-sorting algorithm on `5` elements, modelled as a (binary) decision tree.
A `leaf p` outputs the permutation `p`; a `node i j l r` compares the keys at positions `i`
and `j` and continues in `l` if `key i ≤ key j`, and in `r` otherwise.  This is the standard
decision-tree model: the algorithm's only access to the input is through comparisons. -/
inductive DTree : Type
  | leaf : Equiv.Perm (Fin 5) → DTree
  | node : Fin 5 → Fin 5 → DTree → DTree → DTree
  deriving Inhabited

namespace DTree

/-- The worst-case number of comparisons performed by the algorithm, i.e. the depth of the
decision tree. -/

theorem card_results_le (t : DTree) : t.results.card ≤ 2 ^ t.depth := by
  induction t with
  | leaf p => simp [results, depth]
  | node i j l r ihl ihr =>
      have h := Finset.card_union_le l.results r.results
      have hl : l.results.card ≤ 2 ^ (max l.depth r.depth) :=
        ihl.trans (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))
      have hr : r.results.card ≤ 2 ^ (max l.depth r.depth) :=
        ihr.trans (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
      calc (results (node i j l r)).card ≤ l.results.card + r.results.card := h
        _ ≤ 2 ^ (max l.depth r.depth) + 2 ^ (max l.depth r.depth) := Nat.add_le_add hl hr
        _ = 2 ^ (depth (node i j l r)) := by rw [depth]; ring

end DTree

/-- Correctness of a comparison sort: on the input whose keys are the ranks given by a
permutation `σ`, the algorithm must output `σ`.  (Only permutation-valued inputs are
required to be sorted correctly, which makes this hypothesis weak, hence the lower bound
below strong.) -/
