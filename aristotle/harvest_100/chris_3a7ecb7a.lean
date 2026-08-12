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
def depth : DTree n α → ℕ
  | leaf _ => 0
  | node _ _ l r => 1 + max l.depth r.depth

/-- Running a decision tree against a comparison oracle `q`, where `q i j` is the answer
to the query "is the element in position `i` at most the element in position `j`?". -/
def run (q : Fin n → Fin n → Bool) : DTree n α → α
  | leaf a => a
  | node i j l r => if q i j then run q l else run q r

/-- The outputs of a decision tree of depth `d` are contained in a set of at most `2 ^ d`
elements (indeed, the set of its leaf labels). -/
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
def oracle {n : ℕ} (key : Fin n → ℕ) : Fin n → Fin n → Bool := fun i j => decide (key i ≤ key j)

/-- A decision tree `t` is a *correct comparison sort* on `n` elements if, for every input
whose relative order is described by the ranking `σ : Equiv.Perm (Fin n)` (position `i` holds
the element of rank `σ i`), running `t` on the comparison oracle of that input outputs `σ`,
i.e. the algorithm determines the ordering of the input. -/
def IsSort {n : ℕ} (t : DTree n (Equiv.Perm (Fin n))) : Prop :=
  ∀ σ : Equiv.Perm (Fin n), t.run (oracle fun i => (σ i : ℕ)) = σ

/-- **Information-theoretic lower bound for comparison sorting of 3 elements.**
Any correct comparison sort of 3 elements performs, in the worst case, at least
`⌈log₂ (3!)⌉ = 3` comparisons. -/
theorem sorting_lb_3 (t : DTree 3 (Equiv.Perm (Fin 3))) (ht : IsSort t) :
    Nat.clog 2 (Nat.factorial 3) ≤ t.depth := by
  classical
  obtain ⟨s, hcard, hmem⟩ := t.exists_output_finset
  have huniv : (Finset.univ : Finset (Equiv.Perm (Fin 3))) ⊆ s := by
    intro σ _
    have := ht σ
    exact this ▸ hmem (oracle fun i => (σ i : ℕ))
  have hsix : (Nat.factorial 3) ≤ s.card := by
    have hcardu : (Finset.univ : Finset (Equiv.Perm (Fin 3))).card = Nat.factorial 3 := by
      simp [Finset.card_univ, Fintype.card_perm]
    calc Nat.factorial 3 = (Finset.univ : Finset (Equiv.Perm (Fin 3))).card := hcardu.symm
      _ ≤ s.card := Finset.card_le_card huniv
  have : Nat.factorial 3 ≤ 2 ^ t.depth := le_trans hsix hcard
  exact (Nat.clog_le_iff_le_pow (by norm_num)).2 this

/-- Sanity check: `⌈log₂ (3!)⌉ = 3`, so the bound above really says "at least 3 comparisons". -/
theorem clog_two_factorial_three : Nat.clog 2 (Nat.factorial 3) = 3 := by
  norm_num [Nat.factorial]

/-- Restatement: any correct comparison sort of 3 elements needs at least 3 comparisons
in the worst case. -/
theorem sorting_lb_3' (t : DTree 3 (Equiv.Perm (Fin 3))) (ht : IsSort t) : 3 ≤ t.depth := by
  have := sorting_lb_3 t ht
  rwa [clog_two_factorial_three] at this

/-- An explicit comparison sort of 3 elements using at most 3 comparisons: it first compares
positions `0` and `1`, and then resolves the remaining ambiguity with at most two further
comparisons. -/
def sort3 : DTree 3 (Equiv.Perm (Fin 3)) :=
  .node 0 1
    (.node 1 2
      (.leaf 1)
      (.node 0 2
        (.leaf (Equiv.swap 1 2))
        (.leaf (Equiv.swap 0 1 * Equiv.swap 1 2))))
    (.node 0 2
      (.leaf (Equiv.swap 0 1))
      (.node 1 2
        (.leaf (Equiv.swap 1 2 * Equiv.swap 0 1))
        (.leaf (Equiv.swap 0 2))))

attribute [-instance] Classical.propDecidable in
theorem isSort_sort3 : IsSort sort3 := by
  intro σ; revert σ; decide

theorem depth_sort3 : sort3.depth = 3 := by
  decide

/-- The lower bound is attained: there is a correct comparison sort of 3 elements performing
exactly 3 comparisons in the worst case. In particular the hypothesis `IsSort t` of
`CS.sorting_lb_3` is satisfiable, so that statement is not vacuous. -/
theorem sorting_optimal_3 : ∃ t : DTree 3 (Equiv.Perm (Fin 3)), IsSort t ∧ t.depth = 3 :=
  ⟨sort3, isSort_sort3, depth_sort3⟩

end CS

