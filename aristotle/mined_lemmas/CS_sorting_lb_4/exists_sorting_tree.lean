/-
# Sorting Lb 4
Category: Computer Science
Target: CS.sorting_lb_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sorting Lb 4
Category: Computer Science
Target: CS.sorting_lb_4
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

namespace CS

/-- A comparison-based sorting algorithm on 4 elements, modelled as a (binary) decision tree.
A `node i j l r` performs the comparison "is the element in position `i` smaller than or equal
to the element in position `j`?" and continues in the subtree `l` (resp. `r`) if the answer is
yes (resp. no).  A `leaf q` reports that the input arrangement is `q`.
The model is fully adaptive: the comparison performed at each step may depend on all previous
answers. -/
inductive CompTree : Type
  | leaf : Equiv.Perm (Fin 4) → CompTree
  | node : Fin 4 → Fin 4 → CompTree → CompTree → CompTree

namespace CompTree

/-- The worst-case number of comparisons performed by the algorithm, i.e. the depth of the tree. -/

theorem exists_sorting_tree : ∃ t : CompTree, t.Sorts := by
  obtain ⟨t, ht⟩ := CompTree.exists_tree_correct_on Finset.univ
  exact ⟨t, fun p => ht p (Finset.mem_univ p)⟩

/-- `⌈log₂ (4!)⌉ = 5`. -/
