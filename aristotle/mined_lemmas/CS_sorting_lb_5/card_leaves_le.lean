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
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace CS

/-- A *comparison sorting algorithm* on `n` real-valued keys, modelled as a decision tree.
Each internal node `node i j l r` compares the keys at positions `i` and `j` of the input and
branches to `l` if `a i ≤ a j`, to `r` otherwise; each leaf outputs a permutation of the
positions (the claimed sorting order).  Only comparisons of input keys are allowed. -/
inductive CompTree (n : ℕ) : Type
  | leaf : Equiv.Perm (Fin n) → CompTree n
  | node : Fin n → Fin n → CompTree n → CompTree n → CompTree n

namespace CompTree

variable {n : ℕ}

/-- The permutation output by the algorithm on the input `a`. -/

theorem card_leaves_le (t : CompTree n) : t.leaves.card ≤ 2 ^ t.depth := by
  induction t with
  | leaf σ => simp [leaves, depth]
  | node i j l r ihl ihr =>
      refine le_trans (Finset.card_union_le _ _) ?_
      have hl : l.leaves.card ≤ 2 ^ (max l.depth r.depth) :=
        ihl.trans (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))
      have hr : r.leaves.card ≤ 2 ^ (max l.depth r.depth) :=
        ihr.trans (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
      have : l.leaves.card + r.leaves.card ≤
          2 ^ (max l.depth r.depth) + 2 ^ (max l.depth r.depth) := by omega
      simpa [depth, pow_succ, two_mul, Nat.mul_comm] using this

/-- Every output of the algorithm occurs as a leaf. -/
