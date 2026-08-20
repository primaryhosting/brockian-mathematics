/-
# Sorting Lb 3
Category: Computer Science
Target: CS.sorting_lb_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace CS

/-- A comparison-based decision tree for sorting `3` elements.

An internal node `cmp i j l r` performs the comparison "is the element at position `i`
smaller than the element at position `j`?" and branches accordingly; a leaf reports the
permutation that the algorithm claims describes the input order. -/
inductive DTree3 : Type
  | leaf (out : Equiv.Perm (Fin 3)) : DTree3
  | cmp (i j : Fin 3) (l r : DTree3) : DTree3
  deriving Inhabited

namespace DTree3

/-- The worst-case number of comparisons performed by the decision tree, i.e. its depth. -/

lemma card_outputs_le (t : DTree3) : (outputs t).card ≤ 2 ^ depth t := by
  induction t with
  | leaf o => simp [outputs, depth]
  | cmp i j l r ihl ihr =>
      have h1 : (outputs l ∪ outputs r).card ≤ (outputs l).card + (outputs r).card :=
        Finset.card_union_le _ _
      have h2 : (outputs l).card ≤ 2 ^ max (depth l) (depth r) :=
        ihl.trans (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))
      have h3 : (outputs r).card ≤ 2 ^ max (depth l) (depth r) :=
        ihr.trans (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
      have : (outputs (cmp i j l r)).card ≤ 2 ^ max (depth l) (depth r)
          + 2 ^ max (depth l) (depth r) := by
        simpa [outputs] using h1.trans (Nat.add_le_add h2 h3)
      simpa [depth, pow_succ, Nat.mul_two] using this

/-- A sorting decision tree must have all `3! = 6` permutations among its leaf outputs. -/
