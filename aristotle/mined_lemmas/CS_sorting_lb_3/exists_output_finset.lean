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

/-! # Information-theoretic lower bound for comparison sorting of 3 elements

We model a comparison-based sorting algorithm on `n` elements as a binary decision tree.
An internal node is a comparison query of two input positions `(i, j)`, whose two subtrees
are followed according to the (boolean) answer; a leaf is labelled with the answer the
algorithm outputs (the permutation that sorts the input).

The worst-case number of comparisons performed by the algorithm is the depth of the tree.

For `n = 3` we prove that any correct comparison sort has depth at least
`⌈log₂ (3!)⌉ = Nat.clog 2 (3!) = 3`.
-/

/-- A comparison decision tree on `n` positions with answers in `α`:
either a leaf carrying an output, or a comparison of two positions with the
two continuation subtrees. -/
inductive DTree (n : ℕ) (α : Type*) where
  | leaf : α → DTree n α
  | node : Fin n → Fin n → DTree n α → DTree n α → DTree n α
  deriving Inhabited

namespace DTree

variable {n : ℕ} {α : Type*}

/-- The depth of a decision tree: the worst-case number of comparisons it performs. -/

theorem exists_output_finset [DecidableEq α] (t : DTree n α) :
    ∃ s : Finset α, s.card ≤ 2 ^ t.depth ∧ ∀ q : Fin n → Fin n → Bool, t.run q ∈ s := by
  induction t with
  | leaf a => exact ⟨{a}, by simp [depth], by simp [run]⟩
  | node i j l r ihl ihr =>
      obtain ⟨sl, hlcard, hlmem⟩ := ihl
      obtain ⟨sr, hrcard, hrmem⟩ := ihr
      refine ⟨sl ∪ sr, ?_, ?_⟩
      · have h1 : (sl ∪ sr).card ≤ sl.card + sr.card := Finset.card_union_le _ _
        have h2 : sl.card + sr.card ≤ 2 ^ (max l.depth r.depth) + 2 ^ (max l.depth r.depth) :=
          Nat.add_le_add
            (hlcard.trans (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)))
            (hrcard.trans (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)))
        have h3 : 2 ^ (max l.depth r.depth) + 2 ^ (max l.depth r.depth)
            = 2 ^ (depth (node i j l r)) := by
          simp [depth, pow_succ, Nat.add_comm 1]; omega
        omega
      · intro q
        by_cases h : q i j <;> simp only [run, h, if_true, Finset.mem_union]
        · exact Or.inl (hlmem q)
        · exact Or.inr (hrmem q)

end DTree

/-- The comparison oracle determined by an assignment `key : Fin n → ℕ` of (distinct) keys
to the input positions: the answer to the query `(i, j)` is `key i ≤ key j`. -/
