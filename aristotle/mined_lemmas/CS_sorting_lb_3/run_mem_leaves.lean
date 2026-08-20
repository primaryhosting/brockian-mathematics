import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace CS

/-- A comparison-based decision tree for sorting 3 elements.

An input is a permutation `s : Equiv.Perm (Fin 3)`, thought of as assigning to each
position `i` its rank `s i`.  An internal node `node i j l r` compares the keys at
positions `i` and `j`, descending into `l` if `s i < s j` and into `r` otherwise.
A leaf outputs a permutation, the algorithm's claimed ranking of the input. -/
inductive DTree where
  | leaf : Equiv.Perm (Fin 3) → DTree
  | node : Fin 3 → Fin 3 → DTree → DTree → DTree

namespace DTree

/-- The worst-case number of comparisons performed by the tree, i.e. its height. -/

lemma run_mem_leaves (t : DTree) (s : Equiv.Perm (Fin 3)) : t.run s ∈ t.leaves := by
  induction t with
  | leaf p => simp [run, leaves]
  | node i j l r ihl ihr =>
      by_cases h : s i < s j <;> simp [run, leaves, h, ihl, ihr]

