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

theorem seven_le_depth {t : DTree} (h : Correct t) : 7 ≤ t.depth := by
  have hcard : (Finset.univ : Finset (Equiv.Perm (Fin 5))).card = 120 := by
    simp [Finset.card_univ, Fintype.card_perm, Nat.factorial]
  have h120 : (120 : ℕ) ≤ 2 ^ t.depth := by
    have := t.card_results_le
    rwa [results_eq_univ h, hcard] at this
  by_contra hlt
  push_neg at hlt
  have : (2 : ℕ) ^ t.depth ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

