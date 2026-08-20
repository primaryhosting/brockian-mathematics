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

set_option grind.warning false

namespace CS

/-- A comparison-based decision tree for sorting 4 elements.  A `node i j l r`
compares the keys at positions `i` and `j`, continuing in `l` if the key at `i`
is smaller and in `r` otherwise.  A `leaf p` announces that the input ordering
is the permutation `p`. -/
inductive DTree : Type
  | leaf : Equiv.Perm (Fin 4) → DTree
  | node : Fin 4 → Fin 4 → DTree → DTree → DTree
  deriving Inhabited

namespace DTree

/-- The worst-case number of comparisons performed by a decision tree. -/

theorem sorting_lb_4_tight :
    ∃ t : DTree, (∀ σ : Equiv.Perm (Fin 4), t.run σ = σ) ∧
      t.depth = Nat.clog 2 (Nat.factorial 4) :=
  ⟨optTree, optTree_correct, by rw [optTree_depth, clog_factorial_four]⟩

end CS

