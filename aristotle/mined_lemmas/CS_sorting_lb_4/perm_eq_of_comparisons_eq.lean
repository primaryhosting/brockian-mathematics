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

theorem perm_eq_of_comparisons_eq (p q : Equiv.Perm (Fin 4))
    (h : ∀ i j : Fin 4, p i ≤ p j ↔ q i ≤ q j) : p = q := by
  have hmono : Monotone ⇑(p.symm.trans q) := by
    intro a b hab
    have := (h (p.symm a) (p.symm b)).1 (by simpa using hab)
    simpa using this
  have h1 : p.symm.trans q = 1 := (Equiv.Perm.monotone_iff _).1 hmono
  refine Equiv.ext fun i => ?_
  have := Equiv.ext_iff.1 h1 (p i)
  simpa using this.symm

/-- For every set of arrangements there is a decision tree identifying each of them: repeatedly
split the remaining candidates by a comparison on which two of them disagree. -/
